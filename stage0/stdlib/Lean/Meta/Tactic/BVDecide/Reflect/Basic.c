// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Reflect.Basic
// Imports: public import Std.Data.HashMap public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic import Lean.Data.RArray public import Lean.Meta.Sym.SymM public import Lean.Meta.Tactic.BVDecide.Normalize.Basic
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
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_RArray_ofArray___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RArray_toExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "BVBinOp"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "and"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(67, 200, 193, 54, 191, 172, 208, 119)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__6;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "or"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__8_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__8_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(137, 33, 141, 132, 156, 154, 79, 232)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__9;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "xor"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__10 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__11_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__11_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__11_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(68, 221, 44, 95, 169, 9, 73, 176)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__11 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__12;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__13 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__14_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__14_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__14_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__14_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(236, 85, 182, 141, 252, 28, 21, 198)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__14 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__15;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mul"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__16 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__17_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__17_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__17_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__17_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__16_value),LEAN_SCALAR_PTR_LITERAL(66, 46, 226, 27, 15, 162, 209, 81)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__17 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__17_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__18;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "udiv"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__19 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__20_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__20_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__20_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__20_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__20_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__19_value),LEAN_SCALAR_PTR_LITERAL(97, 106, 189, 172, 252, 249, 116, 143)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__20 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__20_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__21;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "umod"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__22 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__22_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__23_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__23_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__23_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__23_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__23_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__22_value),LEAN_SCALAR_PTR_LITERAL(185, 164, 216, 8, 44, 82, 23, 11)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__23 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__23_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__24;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(173, 0, 131, 50, 199, 91, 123, 28)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BVUnOp"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "not"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__2_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(30, 170, 248, 163, 146, 14, 228, 74)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__3;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "rotateLeft"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(29, 116, 55, 155, 243, 43, 27, 136)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__6;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "rotateRight"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__8_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__8_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(112, 197, 123, 204, 93, 250, 252, 249)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__9;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "arithShiftRightConst"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__10 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__11_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__11_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__11_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(88, 95, 189, 240, 90, 71, 117, 208)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__11 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__12;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "reverse"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__13 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__14_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__14_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__14_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__14_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(84, 226, 239, 81, 45, 17, 252, 180)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__14 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__15;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "clz"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__16 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__17_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__17_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__17_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__17_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__16_value),LEAN_SCALAR_PTR_LITERAL(221, 66, 219, 130, 52, 97, 84, 10)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__17 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__17_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__18;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cpop"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__19 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__20_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__20_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__20_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__20_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__20_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__19_value),LEAN_SCALAR_PTR_LITERAL(214, 119, 73, 246, 51, 241, 221, 59)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__20 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__20_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__21;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 14, 123, 74, 130, 241, 190, 47)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BVExpr"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "var"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__2_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__1_value),LEAN_SCALAR_PTR_LITERAL(158, 7, 174, 153, 9, 234, 93, 144)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__3;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "const"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(213, 213, 79, 77, 131, 135, 136, 165)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__6;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__7_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__7_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__8_value),LEAN_SCALAR_PTR_LITERAL(101, 105, 192, 171, 214, 131, 43, 105)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__9 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__10;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "extract"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__11 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__12_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__12_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__12_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__12_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__12_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__11_value),LEAN_SCALAR_PTR_LITERAL(13, 22, 63, 119, 146, 191, 248, 8)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__12 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__13;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "bin"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__14 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__15_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__15_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__15_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__15_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__15_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__14_value),LEAN_SCALAR_PTR_LITERAL(47, 182, 211, 92, 78, 225, 70, 26)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__15 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__15_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__16;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "un"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__17 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__17_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__18_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__18_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__18_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__18_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__18_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__17_value),LEAN_SCALAR_PTR_LITERAL(42, 186, 200, 92, 180, 128, 216, 181)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__18 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__18_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__19;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__20 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__20_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__21 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__21_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__20_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__22_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__21_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__22 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__22_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__23;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__24;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__25;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__26 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__26_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__26_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__27 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__27_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__28;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "append"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__29 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__29_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__30_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__30_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__30_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__30_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__30_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__29_value),LEAN_SCALAR_PTR_LITERAL(148, 222, 207, 10, 98, 174, 247, 204)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__30 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__30_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__31;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "replicate"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__32 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__32_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__33_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__33_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__33_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__33_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__33_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__32_value),LEAN_SCALAR_PTR_LITERAL(105, 148, 101, 98, 245, 160, 38, 159)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__33 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__33_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__34;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "shiftLeft"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__35 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__35_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__36_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__36_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__36_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__36_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__36_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__35_value),LEAN_SCALAR_PTR_LITERAL(197, 209, 242, 75, 214, 61, 180, 95)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__36 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__36_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__37;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "shiftRight"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__38 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__38_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__39_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__39_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__39_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__39_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__39_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__38_value),LEAN_SCALAR_PTR_LITERAL(71, 199, 243, 56, 253, 18, 242, 226)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__39 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__39_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__40;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "arithShiftRight"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__41 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__41_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__42_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__42_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__42_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__42_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__42_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__41_value),LEAN_SCALAR_PTR_LITERAL(103, 53, 88, 127, 221, 158, 175, 136)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__42 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__42_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__43;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___lam__0(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__0_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__0_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__0_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr(lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "BVBinPred"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "eq"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 174, 16, 156, 11, 3, 67, 199)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__2_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(110, 124, 151, 202, 173, 235, 72, 127)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__3;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ult"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 174, 16, 156, 11, 3, 67, 199)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(64, 63, 119, 185, 54, 210, 178, 92)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 174, 16, 156, 11, 3, 67, 199)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Gate"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 25, 243, 65, 109, 17, 59, 185)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(191, 125, 195, 121, 220, 103, 239, 120)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__2;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 25, 243, 65, 109, 17, 59, 185)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__3_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(64, 67, 164, 147, 7, 85, 189, 57)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__4;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "beq"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__6_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__6_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 25, 243, 65, 109, 17, 59, 185)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__6_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(208, 118, 173, 79, 191, 184, 148, 203)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__7;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__8_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 25, 243, 65, 109, 17, 59, 185)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__8_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(37, 170, 13, 59, 155, 6, 165, 62)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 25, 243, 65, 109, 17, 59, 185)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprGate;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BVPred"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 253, 4, 25, 159, 236, 140, 252)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__14_value),LEAN_SCALAR_PTR_LITERAL(36, 213, 64, 10, 224, 53, 8, 130)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__2;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "getLsbD"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 253, 4, 25, 159, 236, 140, 252)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__4_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(233, 227, 220, 143, 67, 138, 133, 64)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go(lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 253, 4, 25, 159, 236, 140, 252)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVPred;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BoolExpr"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "literal"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 254, 9, 142, 35, 136, 25, 70)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__2_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(124, 170, 215, 35, 43, 27, 202, 11)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__3;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 254, 9, 142, 35, 136, 25, 70)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__4_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__4_value),LEAN_SCALAR_PTR_LITERAL(244, 184, 12, 163, 38, 128, 83, 107)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__5;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__6_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__9;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__12;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__13_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__13_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__13_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 254, 9, 142, 35, 136, 25, 70)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__13_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(244, 134, 245, 64, 53, 182, 217, 215)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__14;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "gate"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__15 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__15_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__16_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__16_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__16_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__16_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 254, 9, 142, 35, 136, 25, 70)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__16_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__15_value),LEAN_SCALAR_PTR_LITERAL(65, 48, 52, 229, 233, 139, 247, 222)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__16 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__16_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__17;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__18 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__19_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__19_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__19_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__19_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 254, 9, 142, 35, 136, 25, 70)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__19_value_aux_3),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__18_value),LEAN_SCALAR_PTR_LITERAL(222, 47, 143, 42, 137, 9, 112, 75)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__19 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__19_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__20;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___lam__0(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__0_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__0_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__0_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 254, 9, 142, 35, 136, 25, 70)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_evalsAtAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_evalsAtAtoms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_M_run_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_M_run_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__2;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_atoms___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_atoms___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_atoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_atoms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "updateAtomsAssignment should only be called when there is an atom"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PackedBitVec"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(53, 26, 122, 246, 246, 235, 136, 91)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___lam__0, .m_arity = 7, .m_num_fixed = 6, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_atomsAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_atomsAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__0;
static const lean_closure_object l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__1;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__2_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__3_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__4_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__7;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "New atom of width "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__9;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = ", synthetic\? "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__10 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__11;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__12 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__13;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Meta.Tactic.BVDecide.Reflect.Basic"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__14 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__14_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.Tactic.BVDecide.M.lookup"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__15 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__15_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "The same atom occurs with different widths, this is a bug"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__16 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__16_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__17;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_lookup(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_lookup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_simplifyTernaryProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_getHyps___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_getHyps___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_getHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_getHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__6(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_12_ = lean_box(0);
v___x_13_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__5));
v___x_14_ = l_Lean_mkConst(v___x_13_, v___x_12_);
return v___x_14_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__9(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_22_ = lean_box(0);
v___x_23_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__8));
v___x_24_ = l_Lean_mkConst(v___x_23_, v___x_22_);
return v___x_24_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__12(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_32_ = lean_box(0);
v___x_33_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__11));
v___x_34_ = l_Lean_mkConst(v___x_33_, v___x_32_);
return v___x_34_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__15(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_42_ = lean_box(0);
v___x_43_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__14));
v___x_44_ = l_Lean_mkConst(v___x_43_, v___x_42_);
return v___x_44_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__18(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = lean_box(0);
v___x_53_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__17));
v___x_54_ = l_Lean_mkConst(v___x_53_, v___x_52_);
return v___x_54_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__21(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = lean_box(0);
v___x_63_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__20));
v___x_64_ = l_Lean_mkConst(v___x_63_, v___x_62_);
return v___x_64_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__24(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_72_ = lean_box(0);
v___x_73_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__23));
v___x_74_ = l_Lean_mkConst(v___x_73_, v___x_72_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0(uint8_t v_x_75_){
_start:
{
switch(v_x_75_)
{
case 0:
{
lean_object* v___x_76_; 
v___x_76_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__6, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__6);
return v___x_76_;
}
case 1:
{
lean_object* v___x_77_; 
v___x_77_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__9, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__9);
return v___x_77_;
}
case 2:
{
lean_object* v___x_78_; 
v___x_78_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__12, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__12);
return v___x_78_;
}
case 3:
{
lean_object* v___x_79_; 
v___x_79_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__15, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__15);
return v___x_79_;
}
case 4:
{
lean_object* v___x_80_; 
v___x_80_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__18, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__18_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__18);
return v___x_80_;
}
case 5:
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__21, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__21);
return v___x_81_;
}
default: 
{
lean_object* v___x_82_; 
v___x_82_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__24, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__24_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__24);
return v___x_82_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___boxed(lean_object* v_x_83_){
_start:
{
uint8_t v_x_boxed_84_; lean_object* v_res_85_; 
v_x_boxed_84_ = lean_unbox(v_x_83_);
v_res_85_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0(v_x_boxed_84_);
return v_res_85_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__2(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_92_ = lean_box(0);
v___x_93_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__1));
v___x_94_ = l_Lean_mkConst(v___x_93_, v___x_92_);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__3(void){
_start:
{
lean_object* v___x_95_; lean_object* v___f_96_; lean_object* v___x_97_; 
v___x_95_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__2, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__2);
v___f_96_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__0));
v___x_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_97_, 0, v___f_96_);
lean_ctor_set(v___x_97_, 1, v___x_95_);
return v___x_97_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp(void){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__3, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__3);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__3(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_107_ = lean_box(0);
v___x_108_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__2));
v___x_109_ = l_Lean_mkConst(v___x_108_, v___x_107_);
return v___x_109_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__6(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_117_ = lean_box(0);
v___x_118_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__5));
v___x_119_ = l_Lean_mkConst(v___x_118_, v___x_117_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__9(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_127_ = lean_box(0);
v___x_128_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__8));
v___x_129_ = l_Lean_mkConst(v___x_128_, v___x_127_);
return v___x_129_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__12(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_137_ = lean_box(0);
v___x_138_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__11));
v___x_139_ = l_Lean_mkConst(v___x_138_, v___x_137_);
return v___x_139_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__15(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = lean_box(0);
v___x_148_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__14));
v___x_149_ = l_Lean_mkConst(v___x_148_, v___x_147_);
return v___x_149_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__18(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = lean_box(0);
v___x_158_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__17));
v___x_159_ = l_Lean_mkConst(v___x_158_, v___x_157_);
return v___x_159_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__21(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_167_ = lean_box(0);
v___x_168_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__20));
v___x_169_ = l_Lean_mkConst(v___x_168_, v___x_167_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0(lean_object* v_x_170_){
_start:
{
switch(lean_obj_tag(v_x_170_))
{
case 0:
{
lean_object* v___x_171_; 
v___x_171_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__3, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__3);
return v___x_171_;
}
case 1:
{
lean_object* v_n_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_n_172_ = lean_ctor_get(v_x_170_, 0);
lean_inc(v_n_172_);
lean_dec_ref_known(v_x_170_, 1);
v___x_173_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__6, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__6);
v___x_174_ = l_Lean_mkNatLit(v_n_172_);
v___x_175_ = l_Lean_Expr_app___override(v___x_173_, v___x_174_);
return v___x_175_;
}
case 2:
{
lean_object* v_n_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_n_176_ = lean_ctor_get(v_x_170_, 0);
lean_inc(v_n_176_);
lean_dec_ref_known(v_x_170_, 1);
v___x_177_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__9, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__9);
v___x_178_ = l_Lean_mkNatLit(v_n_176_);
v___x_179_ = l_Lean_Expr_app___override(v___x_177_, v___x_178_);
return v___x_179_;
}
case 3:
{
lean_object* v_n_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v_n_180_ = lean_ctor_get(v_x_170_, 0);
lean_inc(v_n_180_);
lean_dec_ref_known(v_x_170_, 1);
v___x_181_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__12, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__12);
v___x_182_ = l_Lean_mkNatLit(v_n_180_);
v___x_183_ = l_Lean_Expr_app___override(v___x_181_, v___x_182_);
return v___x_183_;
}
case 4:
{
lean_object* v___x_184_; 
v___x_184_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__15, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__15);
return v___x_184_;
}
case 5:
{
lean_object* v___x_185_; 
v___x_185_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__18, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__18_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__18);
return v___x_185_;
}
default: 
{
lean_object* v___x_186_; 
v___x_186_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__21, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__21);
return v___x_186_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__2(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_193_ = lean_box(0);
v___x_194_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__1));
v___x_195_ = l_Lean_mkConst(v___x_194_, v___x_193_);
return v___x_195_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__3(void){
_start:
{
lean_object* v___x_196_; lean_object* v___f_197_; lean_object* v___x_198_; 
v___x_196_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__2, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__2);
v___f_197_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__0));
v___x_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_198_, 0, v___f_197_);
lean_ctor_set(v___x_198_, 1, v___x_196_);
return v___x_198_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp(void){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__3, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__3);
return v___x_199_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__3(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_208_ = lean_box(0);
v___x_209_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__2));
v___x_210_ = l_Lean_mkConst(v___x_209_, v___x_208_);
return v___x_210_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__6(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_218_ = lean_box(0);
v___x_219_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__5));
v___x_220_ = l_Lean_mkConst(v___x_219_, v___x_218_);
return v___x_220_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__10(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_226_ = lean_box(0);
v___x_227_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__9));
v___x_228_ = l_Lean_Expr_const___override(v___x_227_, v___x_226_);
return v___x_228_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__13(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_236_ = lean_box(0);
v___x_237_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__12));
v___x_238_ = l_Lean_mkConst(v___x_237_, v___x_236_);
return v___x_238_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__16(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_246_ = lean_box(0);
v___x_247_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__15));
v___x_248_ = l_Lean_mkConst(v___x_247_, v___x_246_);
return v___x_248_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__19(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_256_ = lean_box(0);
v___x_257_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__18));
v___x_258_ = l_Lean_mkConst(v___x_257_, v___x_256_);
return v___x_258_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__23(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lean_unsigned_to_nat(1u);
v___x_265_ = l_Lean_Level_ofNat(v___x_264_);
return v___x_265_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__24(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_266_ = lean_box(0);
v___x_267_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__23, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__23_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__23);
v___x_268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v___x_266_);
return v___x_268_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__25(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_269_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__24, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__24_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__24);
v___x_270_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__22));
v___x_271_ = l_Lean_mkConst(v___x_270_, v___x_269_);
return v___x_271_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__28(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = lean_box(0);
v___x_276_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__27));
v___x_277_ = l_Lean_mkConst(v___x_276_, v___x_275_);
return v___x_277_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__31(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = lean_box(0);
v___x_286_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__30));
v___x_287_ = l_Lean_mkConst(v___x_286_, v___x_285_);
return v___x_287_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__34(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_295_ = lean_box(0);
v___x_296_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__33));
v___x_297_ = l_Lean_mkConst(v___x_296_, v___x_295_);
return v___x_297_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__37(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_305_ = lean_box(0);
v___x_306_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__36));
v___x_307_ = l_Lean_mkConst(v___x_306_, v___x_305_);
return v___x_307_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__40(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_315_ = lean_box(0);
v___x_316_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__39));
v___x_317_ = l_Lean_mkConst(v___x_316_, v___x_315_);
return v___x_317_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__43(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_325_ = lean_box(0);
v___x_326_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__42));
v___x_327_ = l_Lean_mkConst(v___x_326_, v___x_325_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(lean_object* v_w_328_, lean_object* v_a_329_){
_start:
{
switch(lean_obj_tag(v_a_329_))
{
case 0:
{
lean_object* v_idx_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v_idx_330_ = lean_ctor_get(v_a_329_, 1);
lean_inc(v_idx_330_);
lean_dec_ref_known(v_a_329_, 2);
v___x_331_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__3, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__3);
v___x_332_ = l_Lean_mkNatLit(v_w_328_);
v___x_333_ = l_Lean_mkNatLit(v_idx_330_);
v___x_334_ = l_Lean_mkAppB(v___x_331_, v___x_332_, v___x_333_);
return v___x_334_;
}
case 1:
{
lean_object* v_val_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v_val_335_ = lean_ctor_get(v_a_329_, 1);
lean_inc(v_val_335_);
lean_dec_ref_known(v_a_329_, 2);
v___x_336_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__6, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__6);
v___x_337_ = l_Lean_mkNatLit(v_w_328_);
v___x_338_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__10, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__10);
v___x_339_ = l_Lean_mkNatLit(v_val_335_);
lean_inc_ref(v___x_337_);
v___x_340_ = l_Lean_mkAppB(v___x_338_, v___x_337_, v___x_339_);
v___x_341_ = l_Lean_mkAppB(v___x_336_, v___x_337_, v___x_340_);
return v___x_341_;
}
case 2:
{
lean_object* v_w_342_; lean_object* v_start_343_; lean_object* v_expr_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v_w_342_ = lean_ctor_get(v_a_329_, 0);
lean_inc_n(v_w_342_, 2);
v_start_343_ = lean_ctor_get(v_a_329_, 1);
lean_inc(v_start_343_);
v_expr_344_ = lean_ctor_get(v_a_329_, 3);
lean_inc_ref(v_expr_344_);
lean_dec_ref_known(v_a_329_, 4);
v___x_345_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__13, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__13);
v___x_346_ = l_Lean_mkNatLit(v_w_342_);
v___x_347_ = l_Lean_mkNatLit(v_start_343_);
v___x_348_ = l_Lean_mkNatLit(v_w_328_);
v___x_349_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_342_, v_expr_344_);
v___x_350_ = l_Lean_mkApp4(v___x_345_, v___x_346_, v___x_347_, v___x_348_, v___x_349_);
return v___x_350_;
}
case 3:
{
lean_object* v_lhs_351_; uint8_t v_op_352_; lean_object* v_rhs_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___y_358_; 
v_lhs_351_ = lean_ctor_get(v_a_329_, 1);
lean_inc_ref(v_lhs_351_);
v_op_352_ = lean_ctor_get_uint8(v_a_329_, sizeof(void*)*3 + 8);
v_rhs_353_ = lean_ctor_get(v_a_329_, 2);
lean_inc_ref(v_rhs_353_);
lean_dec_ref_known(v_a_329_, 3);
v___x_354_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__16, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__16_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__16);
lean_inc_n(v_w_328_, 2);
v___x_355_ = l_Lean_mkNatLit(v_w_328_);
v___x_356_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_328_, v_lhs_351_);
switch(v_op_352_)
{
case 0:
{
lean_object* v___x_361_; 
v___x_361_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__6, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__6);
v___y_358_ = v___x_361_;
goto v___jp_357_;
}
case 1:
{
lean_object* v___x_362_; 
v___x_362_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__9, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__9);
v___y_358_ = v___x_362_;
goto v___jp_357_;
}
case 2:
{
lean_object* v___x_363_; 
v___x_363_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__12, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__12);
v___y_358_ = v___x_363_;
goto v___jp_357_;
}
case 3:
{
lean_object* v___x_364_; 
v___x_364_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__15, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__15);
v___y_358_ = v___x_364_;
goto v___jp_357_;
}
case 4:
{
lean_object* v___x_365_; 
v___x_365_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__18, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__18_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__18);
v___y_358_ = v___x_365_;
goto v___jp_357_;
}
case 5:
{
lean_object* v___x_366_; 
v___x_366_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__21, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__21);
v___y_358_ = v___x_366_;
goto v___jp_357_;
}
default: 
{
lean_object* v___x_367_; 
v___x_367_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__24, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__24_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__24);
v___y_358_ = v___x_367_;
goto v___jp_357_;
}
}
v___jp_357_:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_328_, v_rhs_353_);
lean_inc_ref(v___y_358_);
v___x_360_ = l_Lean_mkApp4(v___x_354_, v___x_355_, v___x_356_, v___y_358_, v___x_359_);
return v___x_360_;
}
}
case 4:
{
lean_object* v_op_368_; lean_object* v_operand_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___y_373_; 
v_op_368_ = lean_ctor_get(v_a_329_, 1);
lean_inc(v_op_368_);
v_operand_369_ = lean_ctor_get(v_a_329_, 2);
lean_inc_ref(v_operand_369_);
lean_dec_ref_known(v_a_329_, 3);
v___x_370_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__19, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__19_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__19);
lean_inc(v_w_328_);
v___x_371_ = l_Lean_mkNatLit(v_w_328_);
switch(lean_obj_tag(v_op_368_))
{
case 0:
{
lean_object* v___x_376_; 
v___x_376_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__3, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__3);
v___y_373_ = v___x_376_;
goto v___jp_372_;
}
case 1:
{
lean_object* v_n_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_n_377_ = lean_ctor_get(v_op_368_, 0);
lean_inc(v_n_377_);
lean_dec_ref_known(v_op_368_, 1);
v___x_378_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__6, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__6);
v___x_379_ = l_Lean_mkNatLit(v_n_377_);
v___x_380_ = l_Lean_Expr_app___override(v___x_378_, v___x_379_);
v___y_373_ = v___x_380_;
goto v___jp_372_;
}
case 2:
{
lean_object* v_n_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v_n_381_ = lean_ctor_get(v_op_368_, 0);
lean_inc(v_n_381_);
lean_dec_ref_known(v_op_368_, 1);
v___x_382_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__9, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__9);
v___x_383_ = l_Lean_mkNatLit(v_n_381_);
v___x_384_ = l_Lean_Expr_app___override(v___x_382_, v___x_383_);
v___y_373_ = v___x_384_;
goto v___jp_372_;
}
case 3:
{
lean_object* v_n_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v_n_385_ = lean_ctor_get(v_op_368_, 0);
lean_inc(v_n_385_);
lean_dec_ref_known(v_op_368_, 1);
v___x_386_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__12, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__12);
v___x_387_ = l_Lean_mkNatLit(v_n_385_);
v___x_388_ = l_Lean_Expr_app___override(v___x_386_, v___x_387_);
v___y_373_ = v___x_388_;
goto v___jp_372_;
}
case 4:
{
lean_object* v___x_389_; 
v___x_389_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__15, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__15);
v___y_373_ = v___x_389_;
goto v___jp_372_;
}
case 5:
{
lean_object* v___x_390_; 
v___x_390_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__18, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__18_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__18);
v___y_373_ = v___x_390_;
goto v___jp_372_;
}
default: 
{
lean_object* v___x_391_; 
v___x_391_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__21, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__21);
v___y_373_ = v___x_391_;
goto v___jp_372_;
}
}
v___jp_372_:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_328_, v_operand_369_);
v___x_375_ = l_Lean_mkApp3(v___x_370_, v___x_371_, v___y_373_, v___x_374_);
return v___x_375_;
}
}
case 5:
{
lean_object* v_l_392_; lean_object* v_r_393_; lean_object* v_lhs_394_; lean_object* v_rhs_395_; lean_object* v_wExpr_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v_proof_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v_l_392_ = lean_ctor_get(v_a_329_, 0);
lean_inc_n(v_l_392_, 2);
v_r_393_ = lean_ctor_get(v_a_329_, 1);
lean_inc_n(v_r_393_, 2);
v_lhs_394_ = lean_ctor_get(v_a_329_, 3);
lean_inc_ref(v_lhs_394_);
v_rhs_395_ = lean_ctor_get(v_a_329_, 4);
lean_inc_ref(v_rhs_395_);
lean_dec_ref_known(v_a_329_, 5);
v_wExpr_396_ = l_Lean_mkNatLit(v_w_328_);
v___x_397_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__25, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__25_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__25);
v___x_398_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__28, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__28);
lean_inc_ref(v_wExpr_396_);
v_proof_399_ = l_Lean_mkAppB(v___x_397_, v___x_398_, v_wExpr_396_);
v___x_400_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__31, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__31_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__31);
v___x_401_ = l_Lean_mkNatLit(v_l_392_);
v___x_402_ = l_Lean_mkNatLit(v_r_393_);
v___x_403_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_l_392_, v_lhs_394_);
v___x_404_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_r_393_, v_rhs_395_);
v___x_405_ = l_Lean_mkApp6(v___x_400_, v___x_401_, v___x_402_, v_wExpr_396_, v___x_403_, v___x_404_, v_proof_399_);
return v___x_405_;
}
case 6:
{
lean_object* v_w_406_; lean_object* v_n_407_; lean_object* v_expr_408_; lean_object* v_newWExpr_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v_proof_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v_w_406_ = lean_ctor_get(v_a_329_, 0);
lean_inc_n(v_w_406_, 2);
v_n_407_ = lean_ctor_get(v_a_329_, 2);
lean_inc(v_n_407_);
v_expr_408_ = lean_ctor_get(v_a_329_, 3);
lean_inc_ref(v_expr_408_);
lean_dec_ref_known(v_a_329_, 4);
v_newWExpr_409_ = l_Lean_mkNatLit(v_w_328_);
v___x_410_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__25, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__25_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__25);
v___x_411_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__28, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__28);
lean_inc_ref(v_newWExpr_409_);
v_proof_412_ = l_Lean_mkAppB(v___x_410_, v___x_411_, v_newWExpr_409_);
v___x_413_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__34, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__34_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__34);
v___x_414_ = l_Lean_mkNatLit(v_w_406_);
v___x_415_ = l_Lean_mkNatLit(v_n_407_);
v___x_416_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_406_, v_expr_408_);
v___x_417_ = l_Lean_mkApp5(v___x_413_, v___x_414_, v_newWExpr_409_, v___x_415_, v___x_416_, v_proof_412_);
return v___x_417_;
}
case 7:
{
lean_object* v_n_418_; lean_object* v_lhs_419_; lean_object* v_rhs_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v_n_418_ = lean_ctor_get(v_a_329_, 1);
lean_inc_n(v_n_418_, 2);
v_lhs_419_ = lean_ctor_get(v_a_329_, 2);
lean_inc_ref(v_lhs_419_);
v_rhs_420_ = lean_ctor_get(v_a_329_, 3);
lean_inc_ref(v_rhs_420_);
lean_dec_ref_known(v_a_329_, 4);
v___x_421_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__37, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__37_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__37);
lean_inc(v_w_328_);
v___x_422_ = l_Lean_mkNatLit(v_w_328_);
v___x_423_ = l_Lean_mkNatLit(v_n_418_);
v___x_424_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_328_, v_lhs_419_);
v___x_425_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_n_418_, v_rhs_420_);
v___x_426_ = l_Lean_mkApp4(v___x_421_, v___x_422_, v___x_423_, v___x_424_, v___x_425_);
return v___x_426_;
}
case 8:
{
lean_object* v_n_427_; lean_object* v_lhs_428_; lean_object* v_rhs_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v_n_427_ = lean_ctor_get(v_a_329_, 1);
lean_inc_n(v_n_427_, 2);
v_lhs_428_ = lean_ctor_get(v_a_329_, 2);
lean_inc_ref(v_lhs_428_);
v_rhs_429_ = lean_ctor_get(v_a_329_, 3);
lean_inc_ref(v_rhs_429_);
lean_dec_ref_known(v_a_329_, 4);
v___x_430_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__40, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__40_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__40);
lean_inc(v_w_328_);
v___x_431_ = l_Lean_mkNatLit(v_w_328_);
v___x_432_ = l_Lean_mkNatLit(v_n_427_);
v___x_433_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_328_, v_lhs_428_);
v___x_434_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_n_427_, v_rhs_429_);
v___x_435_ = l_Lean_mkApp4(v___x_430_, v___x_431_, v___x_432_, v___x_433_, v___x_434_);
return v___x_435_;
}
default: 
{
lean_object* v_n_436_; lean_object* v_lhs_437_; lean_object* v_rhs_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v_n_436_ = lean_ctor_get(v_a_329_, 1);
lean_inc_n(v_n_436_, 2);
v_lhs_437_ = lean_ctor_get(v_a_329_, 2);
lean_inc_ref(v_lhs_437_);
v_rhs_438_ = lean_ctor_get(v_a_329_, 3);
lean_inc_ref(v_rhs_438_);
lean_dec_ref_known(v_a_329_, 4);
v___x_439_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__43, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__43_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__43);
lean_inc(v_w_328_);
v___x_440_ = l_Lean_mkNatLit(v_w_328_);
v___x_441_ = l_Lean_mkNatLit(v_n_436_);
v___x_442_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_328_, v_lhs_437_);
v___x_443_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_n_436_, v_rhs_438_);
v___x_444_ = l_Lean_mkApp4(v___x_439_, v___x_440_, v___x_441_, v___x_442_, v___x_443_);
return v___x_444_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___lam__0(lean_object* v_w_445_, lean_object* v_x_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_445_, v_x_446_);
return v___x_447_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__1(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_453_ = lean_box(0);
v___x_454_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__0));
v___x_455_ = l_Lean_mkConst(v___x_454_, v___x_453_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr(lean_object* v_w_456_){
_start:
{
lean_object* v___f_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
lean_inc(v_w_456_);
v___f_457_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___lam__0), 2, 1);
lean_closure_set(v___f_457_, 0, v_w_456_);
v___x_458_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__1, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__1);
v___x_459_ = l_Lean_mkNatLit(v_w_456_);
v___x_460_ = l_Lean_Expr_app___override(v___x_458_, v___x_459_);
v___x_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_461_, 0, v___f_457_);
lean_ctor_set(v___x_461_, 1, v___x_460_);
return v___x_461_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__3(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_470_ = lean_box(0);
v___x_471_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__2));
v___x_472_ = l_Lean_mkConst(v___x_471_, v___x_470_);
return v___x_472_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__6(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_480_ = lean_box(0);
v___x_481_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__5));
v___x_482_ = l_Lean_mkConst(v___x_481_, v___x_480_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0(uint8_t v_x_483_){
_start:
{
if (v_x_483_ == 0)
{
lean_object* v___x_484_; 
v___x_484_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__3, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__3);
return v___x_484_;
}
else
{
lean_object* v___x_485_; 
v___x_485_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__6, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__6);
return v___x_485_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___boxed(lean_object* v_x_486_){
_start:
{
uint8_t v_x_boxed_487_; lean_object* v_res_488_; 
v_x_boxed_487_ = lean_unbox(v_x_486_);
v_res_488_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0(v_x_boxed_487_);
return v_res_488_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__2(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_495_ = lean_box(0);
v___x_496_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__1));
v___x_497_ = l_Lean_mkConst(v___x_496_, v___x_495_);
return v___x_497_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__3(void){
_start:
{
lean_object* v___x_498_; lean_object* v___f_499_; lean_object* v___x_500_; 
v___x_498_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__2, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__2);
v___f_499_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__0));
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v___f_499_);
lean_ctor_set(v___x_500_, 1, v___x_498_);
return v___x_500_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred(void){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__3, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__3);
return v___x_501_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__2(void){
_start:
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_509_ = lean_box(0);
v___x_510_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__1));
v___x_511_ = l_Lean_mkConst(v___x_510_, v___x_509_);
return v___x_511_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__4(void){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_518_ = lean_box(0);
v___x_519_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__3));
v___x_520_ = l_Lean_mkConst(v___x_519_, v___x_518_);
return v___x_520_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__7(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_528_ = lean_box(0);
v___x_529_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__6));
v___x_530_ = l_Lean_mkConst(v___x_529_, v___x_528_);
return v___x_530_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__9(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_537_ = lean_box(0);
v___x_538_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__8));
v___x_539_ = l_Lean_mkConst(v___x_538_, v___x_537_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0(uint8_t v_x_540_){
_start:
{
switch(v_x_540_)
{
case 0:
{
lean_object* v___x_541_; 
v___x_541_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__2);
return v___x_541_;
}
case 1:
{
lean_object* v___x_542_; 
v___x_542_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__4, &l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__4);
return v___x_542_;
}
case 2:
{
lean_object* v___x_543_; 
v___x_543_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__7, &l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__7);
return v___x_543_;
}
default: 
{
lean_object* v___x_544_; 
v___x_544_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__9, &l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__9);
return v___x_544_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___boxed(lean_object* v_x_545_){
_start:
{
uint8_t v_x_boxed_546_; lean_object* v_res_547_; 
v_x_boxed_546_ = lean_unbox(v_x_545_);
v_res_547_ = l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0(v_x_boxed_546_);
return v_res_547_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__2(void){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_554_ = lean_box(0);
v___x_555_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__1));
v___x_556_ = l_Lean_mkConst(v___x_555_, v___x_554_);
return v___x_556_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__3(void){
_start:
{
lean_object* v___x_557_; lean_object* v___f_558_; lean_object* v___x_559_; 
v___x_557_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__2, &l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__2);
v___f_558_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__0));
v___x_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_559_, 0, v___f_558_);
lean_ctor_set(v___x_559_, 1, v___x_557_);
return v___x_559_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate(void){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__3, &l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__3);
return v___x_560_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__2(void){
_start:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_568_ = lean_box(0);
v___x_569_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__1));
v___x_570_ = l_Lean_mkConst(v___x_569_, v___x_568_);
return v___x_570_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__5(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_578_ = lean_box(0);
v___x_579_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__4));
v___x_580_ = l_Lean_mkConst(v___x_579_, v___x_578_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go(lean_object* v_a_581_){
_start:
{
if (lean_obj_tag(v_a_581_) == 0)
{
lean_object* v_w_582_; lean_object* v_lhs_583_; uint8_t v_op_584_; lean_object* v_rhs_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___y_590_; 
v_w_582_ = lean_ctor_get(v_a_581_, 0);
lean_inc_n(v_w_582_, 3);
v_lhs_583_ = lean_ctor_get(v_a_581_, 1);
lean_inc_ref(v_lhs_583_);
v_op_584_ = lean_ctor_get_uint8(v_a_581_, sizeof(void*)*3);
v_rhs_585_ = lean_ctor_get(v_a_581_, 2);
lean_inc_ref(v_rhs_585_);
lean_dec_ref_known(v_a_581_, 3);
v___x_586_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__2, &l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__2);
v___x_587_ = l_Lean_mkNatLit(v_w_582_);
v___x_588_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_582_, v_lhs_583_);
if (v_op_584_ == 0)
{
lean_object* v___x_593_; 
v___x_593_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__3, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__3);
v___y_590_ = v___x_593_;
goto v___jp_589_;
}
else
{
lean_object* v___x_594_; 
v___x_594_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__6, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__6);
v___y_590_ = v___x_594_;
goto v___jp_589_;
}
v___jp_589_:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_582_, v_rhs_585_);
lean_inc_ref(v___y_590_);
v___x_592_ = l_Lean_mkApp4(v___x_586_, v___x_587_, v___x_588_, v___y_590_, v___x_591_);
return v___x_592_;
}
}
else
{
lean_object* v_w_595_; lean_object* v_expr_596_; lean_object* v_idx_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v_w_595_ = lean_ctor_get(v_a_581_, 0);
lean_inc_n(v_w_595_, 2);
v_expr_596_ = lean_ctor_get(v_a_581_, 1);
lean_inc_ref(v_expr_596_);
v_idx_597_ = lean_ctor_get(v_a_581_, 2);
lean_inc(v_idx_597_);
lean_dec_ref_known(v_a_581_, 3);
v___x_598_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__5, &l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__5);
v___x_599_ = l_Lean_mkNatLit(v_w_595_);
v___x_600_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_595_, v_expr_596_);
v___x_601_ = l_Lean_mkNatLit(v_idx_597_);
v___x_602_ = l_Lean_mkApp3(v___x_598_, v___x_599_, v___x_600_, v___x_601_);
return v___x_602_;
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__2(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_609_ = lean_box(0);
v___x_610_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__1));
v___x_611_ = l_Lean_mkConst(v___x_610_, v___x_609_);
return v___x_611_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__3(void){
_start:
{
lean_object* v___x_612_; lean_object* v___f_613_; lean_object* v___x_614_; 
v___x_612_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__2, &l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__2);
v___f_613_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__0));
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v___f_613_);
lean_ctor_set(v___x_614_, 1, v___x_612_);
return v___x_614_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVPred(void){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__3, &l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__3);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__3(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_624_ = lean_box(0);
v___x_625_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__2));
v___x_626_ = l_Lean_mkConst(v___x_625_, v___x_624_);
return v___x_626_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__5(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_633_ = lean_box(0);
v___x_634_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__4));
v___x_635_ = l_Lean_mkConst(v___x_634_, v___x_633_);
return v___x_635_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__9(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_641_ = lean_box(0);
v___x_642_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__8));
v___x_643_ = l_Lean_mkConst(v___x_642_, v___x_641_);
return v___x_643_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__12(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_648_ = lean_box(0);
v___x_649_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__11));
v___x_650_ = l_Lean_mkConst(v___x_649_, v___x_648_);
return v___x_650_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__14(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_657_ = lean_box(0);
v___x_658_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__13));
v___x_659_ = l_Lean_mkConst(v___x_658_, v___x_657_);
return v___x_659_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__17(void){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_667_ = lean_box(0);
v___x_668_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__16));
v___x_669_ = l_Lean_mkConst(v___x_668_, v___x_667_);
return v___x_669_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__20(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_677_ = lean_box(0);
v___x_678_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__19));
v___x_679_ = l_Lean_mkConst(v___x_678_, v___x_677_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg(lean_object* v_inst_680_, lean_object* v_a_681_){
_start:
{
switch(lean_obj_tag(v_a_681_))
{
case 0:
{
lean_object* v_a_682_; lean_object* v_toExpr_683_; lean_object* v_toTypeExpr_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v_a_682_ = lean_ctor_get(v_a_681_, 0);
lean_inc(v_a_682_);
lean_dec_ref_known(v_a_681_, 1);
v_toExpr_683_ = lean_ctor_get(v_inst_680_, 0);
lean_inc_ref(v_toExpr_683_);
v_toTypeExpr_684_ = lean_ctor_get(v_inst_680_, 1);
lean_inc_ref(v_toTypeExpr_684_);
lean_dec_ref(v_inst_680_);
v___x_685_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__3);
v___x_686_ = lean_apply_1(v_toExpr_683_, v_a_682_);
v___x_687_ = l_Lean_mkAppB(v___x_685_, v_toTypeExpr_684_, v___x_686_);
return v___x_687_;
}
case 1:
{
uint8_t v_a_688_; lean_object* v_toTypeExpr_689_; lean_object* v___x_690_; 
v_a_688_ = lean_ctor_get_uint8(v_a_681_, 0);
lean_dec_ref_known(v_a_681_, 0);
v_toTypeExpr_689_ = lean_ctor_get(v_inst_680_, 1);
lean_inc_ref(v_toTypeExpr_689_);
lean_dec_ref(v_inst_680_);
v___x_690_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__5, &l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__5);
if (v_a_688_ == 0)
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__9, &l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__9);
v___x_692_ = l_Lean_mkAppB(v___x_690_, v_toTypeExpr_689_, v___x_691_);
return v___x_692_;
}
else
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__12, &l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__12);
v___x_694_ = l_Lean_mkAppB(v___x_690_, v_toTypeExpr_689_, v___x_693_);
return v___x_694_;
}
}
case 2:
{
lean_object* v_a_695_; lean_object* v_toTypeExpr_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v_a_695_ = lean_ctor_get(v_a_681_, 0);
lean_inc_ref(v_a_695_);
lean_dec_ref_known(v_a_681_, 1);
v_toTypeExpr_696_ = lean_ctor_get(v_inst_680_, 1);
lean_inc_ref(v_toTypeExpr_696_);
v___x_697_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__14, &l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__14);
v___x_698_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg(v_inst_680_, v_a_695_);
v___x_699_ = l_Lean_mkAppB(v___x_697_, v_toTypeExpr_696_, v___x_698_);
return v___x_699_;
}
case 3:
{
uint8_t v_a_700_; lean_object* v_a_701_; lean_object* v_a_702_; lean_object* v_toTypeExpr_703_; lean_object* v___x_704_; lean_object* v___y_706_; 
v_a_700_ = lean_ctor_get_uint8(v_a_681_, sizeof(void*)*2);
v_a_701_ = lean_ctor_get(v_a_681_, 0);
lean_inc_ref(v_a_701_);
v_a_702_ = lean_ctor_get(v_a_681_, 1);
lean_inc_ref(v_a_702_);
lean_dec_ref_known(v_a_681_, 2);
v_toTypeExpr_703_ = lean_ctor_get(v_inst_680_, 1);
lean_inc_ref(v_toTypeExpr_703_);
v___x_704_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__17, &l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__17);
switch(v_a_700_)
{
case 0:
{
lean_object* v___x_710_; 
v___x_710_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__2);
v___y_706_ = v___x_710_;
goto v___jp_705_;
}
case 1:
{
lean_object* v___x_711_; 
v___x_711_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__4, &l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__4);
v___y_706_ = v___x_711_;
goto v___jp_705_;
}
case 2:
{
lean_object* v___x_712_; 
v___x_712_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__7, &l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__7);
v___y_706_ = v___x_712_;
goto v___jp_705_;
}
default: 
{
lean_object* v___x_713_; 
v___x_713_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__9, &l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__9);
v___y_706_ = v___x_713_;
goto v___jp_705_;
}
}
v___jp_705_:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
lean_inc_ref(v_inst_680_);
v___x_707_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg(v_inst_680_, v_a_701_);
v___x_708_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg(v_inst_680_, v_a_702_);
lean_inc_ref(v___y_706_);
v___x_709_ = l_Lean_mkApp4(v___x_704_, v_toTypeExpr_703_, v___y_706_, v___x_707_, v___x_708_);
return v___x_709_;
}
}
default: 
{
lean_object* v_a_714_; lean_object* v_a_715_; lean_object* v_a_716_; lean_object* v_toTypeExpr_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v_a_714_ = lean_ctor_get(v_a_681_, 0);
lean_inc_ref(v_a_714_);
v_a_715_ = lean_ctor_get(v_a_681_, 1);
lean_inc_ref(v_a_715_);
v_a_716_ = lean_ctor_get(v_a_681_, 2);
lean_inc_ref(v_a_716_);
lean_dec_ref_known(v_a_681_, 3);
v_toTypeExpr_717_ = lean_ctor_get(v_inst_680_, 1);
lean_inc_ref(v_toTypeExpr_717_);
v___x_718_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__20, &l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__20_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__20);
lean_inc_ref_n(v_inst_680_, 2);
v___x_719_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg(v_inst_680_, v_a_714_);
v___x_720_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg(v_inst_680_, v_a_715_);
v___x_721_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg(v_inst_680_, v_a_716_);
v___x_722_ = l_Lean_mkApp4(v___x_718_, v_toTypeExpr_717_, v___x_719_, v___x_720_, v___x_721_);
return v___x_722_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go(lean_object* v_00_u03b1_723_, lean_object* v_inst_724_, lean_object* v_a_725_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg(v_inst_724_, v_a_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___lam__0(lean_object* v_inst_727_, lean_object* v_x_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg(v_inst_727_, v_x_728_);
return v___x_729_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__1(void){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_735_ = lean_box(0);
v___x_736_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__0));
v___x_737_ = l_Lean_mkConst(v___x_736_, v___x_735_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg(lean_object* v_inst_738_){
_start:
{
lean_object* v_toTypeExpr_739_; lean_object* v___f_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_toTypeExpr_739_ = lean_ctor_get(v_inst_738_, 1);
lean_inc_ref(v_toTypeExpr_739_);
v___f_740_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___lam__0), 2, 1);
lean_closure_set(v___f_740_, 0, v_inst_738_);
v___x_741_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__1);
v___x_742_ = l_Lean_Expr_app___override(v___x_741_, v_toTypeExpr_739_);
v___x_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_743_, 0, v___f_740_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr(lean_object* v_00_u03b1_744_, lean_object* v_inst_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg(v_inst_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg(lean_object* v_m_747_, lean_object* v_query_748_, lean_object* v_x_749_, lean_object* v_x_750_, lean_object* v_x_751_){
_start:
{
lean_object* v_zero_752_; uint8_t v_isZero_753_; 
v_zero_752_ = lean_unsigned_to_nat(0u);
v_isZero_753_ = lean_nat_dec_eq(v_x_750_, v_zero_752_);
if (v_isZero_753_ == 1)
{
lean_dec(v_x_751_);
lean_dec(v_x_750_);
if (lean_obj_tag(v_x_749_) == 0)
{
lean_object* v___x_754_; 
v___x_754_ = lean_box(2);
return v___x_754_;
}
else
{
lean_object* v_val_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
v_val_755_ = lean_ctor_get(v_x_749_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v_x_749_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v_x_749_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_val_755_);
lean_dec(v_x_749_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_val_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
else
{
lean_object* v_keyArray_763_; lean_object* v_valueArray_764_; lean_object* v___x_765_; uint8_t v_isSome_766_; 
v_keyArray_763_ = lean_ctor_get(v_m_747_, 1);
v_valueArray_764_ = lean_ctor_get(v_m_747_, 2);
v___x_765_ = lean_array_fget_borrowed(v_keyArray_763_, v_x_751_);
v_isSome_766_ = lean_noption_is_some(v___x_765_);
if (v_isSome_766_ == 0)
{
lean_dec(v_x_750_);
if (lean_obj_tag(v_x_749_) == 0)
{
lean_object* v___x_767_; 
v___x_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_767_, 0, v_x_751_);
return v___x_767_;
}
else
{
lean_object* v_val_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_dec(v_x_751_);
v_val_768_ = lean_ctor_get(v_x_749_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v_x_749_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v_x_749_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_val_768_);
lean_dec(v_x_749_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_val_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
else
{
lean_object* v_one_776_; lean_object* v_n_777_; lean_object* v___y_779_; 
v_one_776_ = lean_unsigned_to_nat(1u);
v_n_777_ = lean_nat_sub(v_x_750_, v_one_776_);
lean_dec(v_x_750_);
if (v_isSome_766_ == 0)
{
goto v___jp_785_;
}
else
{
lean_object* v___x_787_; uint8_t v_isSome_788_; 
v___x_787_ = lean_array_fget_borrowed(v_valueArray_764_, v_x_751_);
v_isSome_788_ = lean_noption_is_some(v___x_787_);
if (v_isSome_788_ == 0)
{
goto v___jp_785_;
}
else
{
lean_object* v_val_789_; size_t v___x_790_; size_t v___x_791_; uint8_t v___x_792_; 
lean_inc(v___x_765_);
v_val_789_ = lean_noption_get(v___x_765_);
v___x_790_ = lean_ptr_addr(v_val_789_);
v___x_791_ = lean_ptr_addr(v_query_748_);
v___x_792_ = lean_usize_dec_eq(v___x_790_, v___x_791_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
lean_dec(v_val_789_);
v___x_793_ = lean_array_get_size(v_keyArray_763_);
v___x_794_ = lean_nat_add(v_x_751_, v_one_776_);
lean_dec(v_x_751_);
v___x_795_ = lean_nat_dec_lt(v___x_794_, v___x_793_);
if (v___x_795_ == 0)
{
lean_dec(v___x_794_);
v_x_750_ = v_n_777_;
v_x_751_ = v_zero_752_;
goto _start;
}
else
{
v_x_750_ = v_n_777_;
v_x_751_ = v___x_794_;
goto _start;
}
}
else
{
lean_object* v_val_798_; lean_object* v___x_799_; 
lean_dec(v_n_777_);
lean_dec(v_x_749_);
lean_inc(v___x_787_);
v_val_798_ = lean_noption_get(v___x_787_);
v___x_799_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_799_, 0, v_x_751_);
lean_ctor_set(v___x_799_, 1, v_val_789_);
lean_ctor_set(v___x_799_, 2, v_val_798_);
return v___x_799_;
}
}
}
v___jp_778_:
{
lean_object* v___x_780_; lean_object* v___x_781_; uint8_t v___x_782_; 
v___x_780_ = lean_array_get_size(v_keyArray_763_);
v___x_781_ = lean_nat_add(v_x_751_, v_one_776_);
lean_dec(v_x_751_);
v___x_782_ = lean_nat_dec_lt(v___x_781_, v___x_780_);
if (v___x_782_ == 0)
{
lean_dec(v___x_781_);
v_x_749_ = v___y_779_;
v_x_750_ = v_n_777_;
v_x_751_ = v_zero_752_;
goto _start;
}
else
{
v_x_749_ = v___y_779_;
v_x_750_ = v_n_777_;
v_x_751_ = v___x_781_;
goto _start;
}
}
v___jp_785_:
{
if (lean_obj_tag(v_x_749_) == 0)
{
lean_object* v___x_786_; 
lean_inc(v_x_751_);
v___x_786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_786_, 0, v_x_751_);
v___y_779_ = v___x_786_;
goto v___jp_778_;
}
else
{
v___y_779_ = v_x_749_;
goto v___jp_778_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg___boxed(lean_object* v_m_800_, lean_object* v_query_801_, lean_object* v_x_802_, lean_object* v_x_803_, lean_object* v_x_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg(v_m_800_, v_query_801_, v_x_802_, v_x_803_, v_x_804_);
lean_dec_ref(v_query_801_);
lean_dec_ref(v_m_800_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(lean_object* v_m_806_, lean_object* v_query_807_){
_start:
{
lean_object* v_keyArray_808_; lean_object* v___x_809_; size_t v___x_810_; size_t v___x_811_; size_t v___x_812_; uint64_t v___x_813_; uint64_t v___x_814_; uint64_t v___x_815_; uint64_t v_fold_816_; uint64_t v___x_817_; uint64_t v___x_818_; uint64_t v___x_819_; size_t v___x_820_; size_t v___x_821_; size_t v___x_822_; size_t v___x_823_; size_t v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v_keyArray_808_ = lean_ctor_get(v_m_806_, 1);
v___x_809_ = lean_array_get_size(v_keyArray_808_);
v___x_810_ = lean_ptr_addr(v_query_807_);
v___x_811_ = ((size_t)3ULL);
v___x_812_ = lean_usize_shift_right(v___x_810_, v___x_811_);
v___x_813_ = lean_usize_to_uint64(v___x_812_);
v___x_814_ = 32ULL;
v___x_815_ = lean_uint64_shift_right(v___x_813_, v___x_814_);
v_fold_816_ = lean_uint64_xor(v___x_813_, v___x_815_);
v___x_817_ = 16ULL;
v___x_818_ = lean_uint64_shift_right(v_fold_816_, v___x_817_);
v___x_819_ = lean_uint64_xor(v_fold_816_, v___x_818_);
v___x_820_ = lean_uint64_to_usize(v___x_819_);
v___x_821_ = lean_usize_of_nat(v___x_809_);
v___x_822_ = ((size_t)1ULL);
v___x_823_ = lean_usize_sub(v___x_821_, v___x_822_);
v___x_824_ = lean_usize_land(v___x_820_, v___x_823_);
v___x_825_ = lean_usize_to_nat(v___x_824_);
v___x_826_ = lean_box(0);
v___x_827_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg(v_m_806_, v_query_807_, v___x_826_, v___x_809_, v___x_825_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg___boxed(lean_object* v_m_828_, lean_object* v_query_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v_m_828_, v_query_829_);
lean_dec_ref(v_query_829_);
lean_dec_ref(v_m_828_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2_spec__4_spec__5___redArg(lean_object* v_b_831_, lean_object* v_acc_832_, lean_object* v_i_833_){
_start:
{
lean_object* v___y_835_; lean_object* v_keyArray_843_; lean_object* v_valueArray_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v_keyArray_843_ = lean_ctor_get(v_b_831_, 1);
v_valueArray_844_ = lean_ctor_get(v_b_831_, 2);
v___x_845_ = lean_array_get_size(v_keyArray_843_);
v___x_846_ = lean_nat_dec_lt(v_i_833_, v___x_845_);
if (v___x_846_ == 0)
{
lean_dec(v_i_833_);
return v_acc_832_;
}
else
{
lean_object* v___x_847_; uint8_t v_isSome_848_; 
v___x_847_ = lean_array_fget_borrowed(v_keyArray_843_, v_i_833_);
v_isSome_848_ = lean_noption_is_some(v___x_847_);
if (v_isSome_848_ == 0)
{
goto v___jp_839_;
}
else
{
lean_object* v___x_849_; uint8_t v_isSome_850_; 
v___x_849_ = lean_array_fget_borrowed(v_valueArray_844_, v_i_833_);
v_isSome_850_ = lean_noption_is_some(v___x_849_);
if (v_isSome_850_ == 0)
{
goto v___jp_839_;
}
else
{
lean_object* v_val_851_; lean_object* v_val_852_; lean_object* v_i_854_; lean_object* v___x_859_; 
lean_inc(v___x_847_);
v_val_851_ = lean_noption_get(v___x_847_);
lean_inc(v___x_849_);
v_val_852_ = lean_noption_get(v___x_849_);
v___x_859_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v_acc_832_, v_val_851_);
switch(lean_obj_tag(v___x_859_))
{
case 0:
{
lean_object* v_index_860_; lean_object* v_size_861_; lean_object* v___x_862_; 
v_index_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_index_860_);
lean_dec_ref_known(v___x_859_, 3);
v_size_861_ = lean_ctor_get(v_acc_832_, 0);
lean_inc(v_size_861_);
v___x_862_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_832_, v_size_861_, v_index_860_, v_val_851_, v_val_852_);
lean_dec(v_index_860_);
v___y_835_ = v___x_862_;
goto v___jp_834_;
}
case 1:
{
lean_object* v_index_863_; 
v_index_863_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_index_863_);
lean_dec_ref_known(v___x_859_, 1);
v_i_854_ = v_index_863_;
goto v___jp_853_;
}
default: 
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = lean_unsigned_to_nat(0u);
v___x_865_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_832_, v___x_864_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_index_866_; 
v_index_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_index_866_);
lean_dec_ref_known(v___x_865_, 1);
v_i_854_ = v_index_866_;
goto v___jp_853_;
}
else
{
lean_dec(v_val_852_);
lean_dec(v_val_851_);
v___y_835_ = v_acc_832_;
goto v___jp_834_;
}
}
}
v___jp_853_:
{
lean_object* v_size_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v_size_855_ = lean_ctor_get(v_acc_832_, 0);
v___x_856_ = lean_unsigned_to_nat(1u);
v___x_857_ = lean_nat_add(v_size_855_, v___x_856_);
v___x_858_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_832_, v___x_857_, v_i_854_, v_val_851_, v_val_852_);
lean_dec(v_i_854_);
v___y_835_ = v___x_858_;
goto v___jp_834_;
}
}
}
}
v___jp_834_:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = lean_unsigned_to_nat(1u);
v___x_837_ = lean_nat_add(v_i_833_, v___x_836_);
lean_dec(v_i_833_);
v_acc_832_ = v___y_835_;
v_i_833_ = v___x_837_;
goto _start;
}
v___jp_839_:
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = lean_unsigned_to_nat(1u);
v___x_841_ = lean_nat_add(v_i_833_, v___x_840_);
lean_dec(v_i_833_);
v_i_833_ = v___x_841_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2_spec__4_spec__5___redArg___boxed(lean_object* v_b_867_, lean_object* v_acc_868_, lean_object* v_i_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2_spec__4_spec__5___redArg(v_b_867_, v_acc_868_, v_i_869_);
lean_dec_ref(v_b_867_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2_spec__4___redArg(lean_object* v_init_871_, lean_object* v_b_872_){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = lean_unsigned_to_nat(0u);
v___x_874_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2_spec__4_spec__5___redArg(v_b_872_, v_init_871_, v___x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2_spec__4___redArg___boxed(lean_object* v_init_875_, lean_object* v_b_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2_spec__4___redArg(v_init_875_, v_b_876_);
lean_dec_ref(v_b_876_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2___redArg(lean_object* v_m_878_){
_start:
{
lean_object* v_keyArray_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v_cellCount_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v_target_886_; lean_object* v___x_887_; 
v_keyArray_879_ = lean_ctor_get(v_m_878_, 1);
v___x_880_ = lean_array_get_size(v_keyArray_879_);
v___x_881_ = lean_unsigned_to_nat(2u);
v_cellCount_882_ = lean_nat_mul(v___x_880_, v___x_881_);
v___x_883_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_882_);
v___x_884_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_882_);
v___x_885_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_882_);
v_target_886_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_886_, 0, v___x_883_);
lean_ctor_set(v_target_886_, 1, v___x_884_);
lean_ctor_set(v_target_886_, 2, v___x_885_);
v___x_887_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2_spec__4___redArg(v_target_886_, v_m_878_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2___redArg___boxed(lean_object* v_m_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2___redArg(v_m_888_);
lean_dec_ref(v_m_888_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg(lean_object* v_m_890_, lean_object* v_query_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v_m_890_, v_query_891_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_index_893_; lean_object* v_key_894_; lean_object* v_value_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
v_index_893_ = lean_ctor_get(v___x_892_, 0);
v_key_894_ = lean_ctor_get(v___x_892_, 1);
v_value_895_ = lean_ctor_get(v___x_892_, 2);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_892_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_value_895_);
lean_inc(v_key_894_);
lean_inc(v_index_893_);
lean_dec(v___x_892_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_index_893_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_key_894_);
lean_ctor_set(v_reuseFailAlloc_901_, 2, v_value_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
else
{
lean_object* v___x_903_; 
lean_dec(v___x_892_);
v___x_903_ = lean_box(1);
return v___x_903_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg___boxed(lean_object* v_m_904_, lean_object* v_query_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg(v_m_904_, v_query_905_);
lean_dec_ref(v_query_905_);
lean_dec_ref(v_m_904_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(lean_object* v_m_907_, lean_object* v_a_908_){
_start:
{
lean_object* v___x_909_; 
v___x_909_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg(v_m_907_, v_a_908_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_value_910_; lean_object* v___x_911_; 
v_value_910_ = lean_ctor_get(v___x_909_, 2);
lean_inc(v_value_910_);
lean_dec_ref_known(v___x_909_, 3);
v___x_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_911_, 0, v_value_910_);
return v___x_911_;
}
else
{
lean_object* v___x_912_; 
v___x_912_ = lean_box(0);
return v___x_912_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg___boxed(lean_object* v_m_913_, lean_object* v_a_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_m_913_, v_a_914_);
lean_dec_ref(v_a_914_);
lean_dec_ref(v_m_913_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(lean_object* v_reified_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_){
_start:
{
lean_object* v___x_926_; lean_object* v_originalExpr_927_; lean_object* v_evalsAtAtoms_x27_928_; lean_object* v_evalsAtCache_929_; lean_object* v___x_930_; 
v___x_926_ = lean_st_ref_get(v_a_918_);
v_originalExpr_927_ = lean_ctor_get(v_reified_916_, 2);
lean_inc_ref(v_originalExpr_927_);
v_evalsAtAtoms_x27_928_ = lean_ctor_get(v_reified_916_, 3);
lean_inc_ref(v_evalsAtAtoms_x27_928_);
lean_dec_ref(v_reified_916_);
v_evalsAtCache_929_ = lean_ctor_get(v___x_926_, 2);
lean_inc_ref(v_evalsAtCache_929_);
lean_dec(v___x_926_);
v___x_930_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_evalsAtCache_929_, v_originalExpr_927_);
lean_dec_ref(v_evalsAtCache_929_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v___x_931_; 
lean_inc(v_a_924_);
lean_inc_ref(v_a_923_);
lean_inc(v_a_922_);
lean_inc_ref(v_a_921_);
lean_inc(v_a_920_);
lean_inc_ref(v_a_919_);
lean_inc(v_a_918_);
lean_inc_ref(v_a_917_);
v___x_931_ = lean_apply_9(v_evalsAtAtoms_x27_928_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, lean_box(0));
if (lean_obj_tag(v___x_931_) == 0)
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_1017_; 
v_a_932_ = lean_ctor_get(v___x_931_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_931_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_934_ = v___x_931_;
v_isShared_935_ = v_isSharedCheck_1017_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_931_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_1017_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_936_; lean_object* v_atoms_937_; lean_object* v_atomsAssignmentCache_938_; lean_object* v_evalsAtCache_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_1016_; 
v___x_936_ = lean_st_ref_take(v_a_918_);
v_atoms_937_ = lean_ctor_get(v___x_936_, 0);
v_atomsAssignmentCache_938_ = lean_ctor_get(v___x_936_, 1);
v_evalsAtCache_939_ = lean_ctor_get(v___x_936_, 2);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_941_ = v___x_936_;
v_isShared_942_ = v_isSharedCheck_1016_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_evalsAtCache_939_);
lean_inc(v_atomsAssignmentCache_938_);
lean_inc(v_atoms_937_);
lean_dec(v___x_936_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_1016_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___y_944_; lean_object* v___y_953_; lean_object* v_i_954_; lean_object* v___y_970_; lean_object* v_i_971_; lean_object* v___y_977_; lean_object* v___x_986_; 
v___x_986_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v_evalsAtCache_939_, v_originalExpr_927_);
switch(lean_obj_tag(v___x_986_))
{
case 0:
{
lean_object* v_index_987_; lean_object* v_size_988_; lean_object* v___x_989_; 
v_index_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_index_987_);
lean_dec_ref_known(v___x_986_, 3);
v_size_988_ = lean_ctor_get(v_evalsAtCache_939_, 0);
lean_inc(v_size_988_);
lean_inc(v_a_932_);
v___x_989_ = l_Std_DHashMap_Raw_setEntry___redArg(v_evalsAtCache_939_, v_size_988_, v_index_987_, v_originalExpr_927_, v_a_932_);
lean_dec(v_index_987_);
v___y_944_ = v___x_989_;
goto v___jp_943_;
}
case 1:
{
lean_object* v_index_990_; lean_object* v_size_991_; lean_object* v_keyArray_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; uint8_t v___x_996_; 
v_index_990_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_index_990_);
lean_dec_ref_known(v___x_986_, 1);
v_size_991_ = lean_ctor_get(v_evalsAtCache_939_, 0);
v_keyArray_992_ = lean_ctor_get(v_evalsAtCache_939_, 1);
v___x_993_ = lean_unsigned_to_nat(1u);
v___x_994_ = lean_nat_add(v_size_991_, v___x_993_);
v___x_995_ = lean_array_get_size(v_keyArray_992_);
v___x_996_ = lean_nat_dec_lt(v___x_994_, v___x_995_);
if (v___x_996_ == 0)
{
lean_dec(v___x_994_);
lean_dec(v_index_990_);
goto v___jp_959_;
}
else
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; 
v___x_997_ = lean_unsigned_to_nat(4u);
v___x_998_ = lean_nat_mul(v___x_994_, v___x_997_);
v___x_999_ = lean_unsigned_to_nat(3u);
v___x_1000_ = lean_nat_mul(v___x_995_, v___x_999_);
v___x_1001_ = lean_nat_dec_le(v___x_998_, v___x_1000_);
lean_dec(v___x_1000_);
lean_dec(v___x_998_);
if (v___x_1001_ == 0)
{
lean_dec(v___x_994_);
lean_dec(v_index_990_);
goto v___jp_959_;
}
else
{
lean_object* v___x_1002_; 
lean_inc(v_a_932_);
v___x_1002_ = l_Std_DHashMap_Raw_setEntry___redArg(v_evalsAtCache_939_, v___x_994_, v_index_990_, v_originalExpr_927_, v_a_932_);
lean_dec(v_index_990_);
v___y_944_ = v___x_1002_;
goto v___jp_943_;
}
}
}
default: 
{
lean_object* v_size_1003_; lean_object* v_keyArray_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; 
v_size_1003_ = lean_ctor_get(v_evalsAtCache_939_, 0);
v_keyArray_1004_ = lean_ctor_get(v_evalsAtCache_939_, 1);
v___x_1005_ = lean_unsigned_to_nat(1u);
v___x_1006_ = lean_nat_add(v_size_1003_, v___x_1005_);
v___x_1007_ = lean_array_get_size(v_keyArray_1004_);
v___x_1008_ = lean_nat_dec_lt(v___x_1006_, v___x_1007_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; 
lean_dec(v___x_1006_);
v___x_1009_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2___redArg(v_evalsAtCache_939_);
lean_dec_ref(v_evalsAtCache_939_);
v___y_977_ = v___x_1009_;
goto v___jp_976_;
}
else
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; 
v___x_1010_ = lean_unsigned_to_nat(4u);
v___x_1011_ = lean_nat_mul(v___x_1006_, v___x_1010_);
lean_dec(v___x_1006_);
v___x_1012_ = lean_unsigned_to_nat(3u);
v___x_1013_ = lean_nat_mul(v___x_1007_, v___x_1012_);
v___x_1014_ = lean_nat_dec_le(v___x_1011_, v___x_1013_);
lean_dec(v___x_1013_);
lean_dec(v___x_1011_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2___redArg(v_evalsAtCache_939_);
lean_dec_ref(v_evalsAtCache_939_);
v___y_977_ = v___x_1015_;
goto v___jp_976_;
}
else
{
v___y_977_ = v_evalsAtCache_939_;
goto v___jp_976_;
}
}
}
}
v___jp_943_:
{
lean_object* v___x_946_; 
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 2, v___y_944_);
v___x_946_ = v___x_941_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_atoms_937_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_atomsAssignmentCache_938_);
lean_ctor_set(v_reuseFailAlloc_951_, 2, v___y_944_);
v___x_946_ = v_reuseFailAlloc_951_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_947_ = lean_st_ref_put(v_a_918_, v___x_946_);
if (v_isShared_935_ == 0)
{
v___x_949_ = v___x_934_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_932_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
v___jp_952_:
{
lean_object* v_size_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v_size_955_ = lean_ctor_get(v___y_953_, 0);
v___x_956_ = lean_unsigned_to_nat(1u);
v___x_957_ = lean_nat_add(v_size_955_, v___x_956_);
lean_inc(v_a_932_);
v___x_958_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_953_, v___x_957_, v_i_954_, v_originalExpr_927_, v_a_932_);
lean_dec(v_i_954_);
v___y_944_ = v___x_958_;
goto v___jp_943_;
}
v___jp_959_:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2___redArg(v_evalsAtCache_939_);
lean_dec_ref(v_evalsAtCache_939_);
v___x_961_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v___x_960_, v_originalExpr_927_);
switch(lean_obj_tag(v___x_961_))
{
case 0:
{
lean_object* v_index_962_; lean_object* v_size_963_; lean_object* v___x_964_; 
v_index_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_index_962_);
lean_dec_ref_known(v___x_961_, 3);
v_size_963_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_size_963_);
lean_inc(v_a_932_);
v___x_964_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_960_, v_size_963_, v_index_962_, v_originalExpr_927_, v_a_932_);
lean_dec(v_index_962_);
v___y_944_ = v___x_964_;
goto v___jp_943_;
}
case 1:
{
lean_object* v_index_965_; 
v_index_965_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_index_965_);
lean_dec_ref_known(v___x_961_, 1);
v___y_953_ = v___x_960_;
v_i_954_ = v_index_965_;
goto v___jp_952_;
}
default: 
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = lean_unsigned_to_nat(0u);
v___x_967_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_960_, v___x_966_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_index_968_; 
v_index_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_index_968_);
lean_dec_ref_known(v___x_967_, 1);
v___y_953_ = v___x_960_;
v_i_954_ = v_index_968_;
goto v___jp_952_;
}
else
{
lean_dec_ref(v_originalExpr_927_);
v___y_944_ = v___x_960_;
goto v___jp_943_;
}
}
}
}
v___jp_969_:
{
lean_object* v_size_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v_size_972_ = lean_ctor_get(v___y_970_, 0);
v___x_973_ = lean_unsigned_to_nat(1u);
v___x_974_ = lean_nat_add(v_size_972_, v___x_973_);
lean_inc(v_a_932_);
v___x_975_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_970_, v___x_974_, v_i_971_, v_originalExpr_927_, v_a_932_);
lean_dec(v_i_971_);
v___y_944_ = v___x_975_;
goto v___jp_943_;
}
v___jp_976_:
{
lean_object* v___x_978_; 
v___x_978_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v___y_977_, v_originalExpr_927_);
switch(lean_obj_tag(v___x_978_))
{
case 0:
{
lean_object* v_index_979_; lean_object* v_size_980_; lean_object* v___x_981_; 
v_index_979_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_index_979_);
lean_dec_ref_known(v___x_978_, 3);
v_size_980_ = lean_ctor_get(v___y_977_, 0);
lean_inc(v_size_980_);
lean_inc(v_a_932_);
v___x_981_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_977_, v_size_980_, v_index_979_, v_originalExpr_927_, v_a_932_);
lean_dec(v_index_979_);
v___y_944_ = v___x_981_;
goto v___jp_943_;
}
case 1:
{
lean_object* v_index_982_; 
v_index_982_ = lean_ctor_get(v___x_978_, 0);
lean_inc(v_index_982_);
lean_dec_ref_known(v___x_978_, 1);
v___y_970_ = v___y_977_;
v_i_971_ = v_index_982_;
goto v___jp_969_;
}
default: 
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = lean_unsigned_to_nat(0u);
v___x_984_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_977_, v___x_983_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_index_985_; 
v_index_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_index_985_);
lean_dec_ref_known(v___x_984_, 1);
v___y_970_ = v___y_977_;
v_i_971_ = v_index_985_;
goto v___jp_969_;
}
else
{
lean_dec_ref(v_originalExpr_927_);
v___y_944_ = v___y_977_;
goto v___jp_943_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_originalExpr_927_);
return v___x_931_;
}
}
else
{
lean_object* v_val_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
lean_dec_ref(v_evalsAtAtoms_x27_928_);
lean_dec_ref(v_originalExpr_927_);
v_val_1018_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_930_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_val_1018_);
lean_dec(v___x_930_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
lean_ctor_set_tag(v___x_1020_, 0);
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_val_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms___boxed(lean_object* v_reified_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(v_reified_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
lean_dec(v_a_1032_);
lean_dec_ref(v_a_1031_);
lean_dec(v_a_1030_);
lean_dec_ref(v_a_1029_);
lean_dec(v_a_1028_);
lean_dec_ref(v_a_1027_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0(lean_object* v_00_u03b2_1037_, lean_object* v_m_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_m_1038_, v_a_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___boxed(lean_object* v_00_u03b2_1041_, lean_object* v_m_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0(v_00_u03b2_1041_, v_m_1042_, v_a_1043_);
lean_dec_ref(v_a_1043_);
lean_dec_ref(v_m_1042_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1(lean_object* v_00_u03b2_1045_, lean_object* v_m_1046_, lean_object* v_query_1047_){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v_m_1046_, v_query_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___boxed(lean_object* v_00_u03b2_1049_, lean_object* v_m_1050_, lean_object* v_query_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1(v_00_u03b2_1049_, v_m_1050_, v_query_1051_);
lean_dec_ref(v_query_1051_);
lean_dec_ref(v_m_1050_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2(lean_object* v_00_u03b2_1053_, lean_object* v_m_1054_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2___redArg(v_m_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2___boxed(lean_object* v_00_u03b2_1056_, lean_object* v_m_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2(v_00_u03b2_1056_, v_m_1057_);
lean_dec_ref(v_m_1057_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0(lean_object* v_00_u03b2_1059_, lean_object* v_m_1060_, lean_object* v_query_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg(v_m_1060_, v_query_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1063_, lean_object* v_m_1064_, lean_object* v_query_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0(v_00_u03b2_1063_, v_m_1064_, v_query_1065_);
lean_dec_ref(v_query_1065_);
lean_dec_ref(v_m_1064_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2(lean_object* v_00_u03b2_1067_, lean_object* v_m_1068_, lean_object* v_query_1069_, lean_object* v_x_1070_, lean_object* v_x_1071_, lean_object* v_x_1072_, lean_object* v_x_1073_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg(v_m_1068_, v_query_1069_, v_x_1070_, v_x_1071_, v_x_1072_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1075_, lean_object* v_m_1076_, lean_object* v_query_1077_, lean_object* v_x_1078_, lean_object* v_x_1079_, lean_object* v_x_1080_, lean_object* v_x_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2(v_00_u03b2_1075_, v_m_1076_, v_query_1077_, v_x_1078_, v_x_1079_, v_x_1080_, v_x_1081_);
lean_dec_ref(v_query_1077_);
lean_dec_ref(v_m_1076_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2_spec__4(lean_object* v_00_u03b2_1083_, lean_object* v_init_1084_, lean_object* v_b_1085_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2_spec__4___redArg(v_init_1084_, v_b_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1087_, lean_object* v_init_1088_, lean_object* v_b_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2_spec__4(v_00_u03b2_1087_, v_init_1088_, v_b_1089_);
lean_dec_ref(v_b_1089_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1091_, lean_object* v_b_1092_, lean_object* v_acc_1093_, lean_object* v_i_1094_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2_spec__4_spec__5___redArg(v_b_1092_, v_acc_1093_, v_i_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2_spec__4_spec__5___boxed(lean_object* v_00_u03b2_1096_, lean_object* v_b_1097_, lean_object* v_acc_1098_, lean_object* v_i_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2_spec__4_spec__5(v_00_u03b2_1096_, v_b_1097_, v_acc_1098_, v_i_1099_);
lean_dec_ref(v_b_1097_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_evalsAtAtoms(lean_object* v_reified_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_){
_start:
{
lean_object* v___x_1111_; lean_object* v_originalExpr_1112_; lean_object* v_evalsAtAtoms_x27_1113_; lean_object* v_evalsAtCache_1114_; lean_object* v___x_1115_; 
v___x_1111_ = lean_st_ref_get(v_a_1103_);
v_originalExpr_1112_ = lean_ctor_get(v_reified_1101_, 1);
lean_inc_ref(v_originalExpr_1112_);
v_evalsAtAtoms_x27_1113_ = lean_ctor_get(v_reified_1101_, 2);
lean_inc_ref(v_evalsAtAtoms_x27_1113_);
lean_dec_ref(v_reified_1101_);
v_evalsAtCache_1114_ = lean_ctor_get(v___x_1111_, 2);
lean_inc_ref(v_evalsAtCache_1114_);
lean_dec(v___x_1111_);
v___x_1115_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_evalsAtCache_1114_, v_originalExpr_1112_);
lean_dec_ref(v_evalsAtCache_1114_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v___x_1116_; 
lean_inc(v_a_1109_);
lean_inc_ref(v_a_1108_);
lean_inc(v_a_1107_);
lean_inc_ref(v_a_1106_);
lean_inc(v_a_1105_);
lean_inc_ref(v_a_1104_);
lean_inc(v_a_1103_);
lean_inc_ref(v_a_1102_);
v___x_1116_ = lean_apply_9(v_evalsAtAtoms_x27_1113_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, lean_box(0));
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1202_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1119_ = v___x_1116_;
v_isShared_1120_ = v_isSharedCheck_1202_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1116_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1202_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1121_; lean_object* v_atoms_1122_; lean_object* v_atomsAssignmentCache_1123_; lean_object* v_evalsAtCache_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1201_; 
v___x_1121_ = lean_st_ref_take(v_a_1103_);
v_atoms_1122_ = lean_ctor_get(v___x_1121_, 0);
v_atomsAssignmentCache_1123_ = lean_ctor_get(v___x_1121_, 1);
v_evalsAtCache_1124_ = lean_ctor_get(v___x_1121_, 2);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1126_ = v___x_1121_;
v_isShared_1127_ = v_isSharedCheck_1201_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_evalsAtCache_1124_);
lean_inc(v_atomsAssignmentCache_1123_);
lean_inc(v_atoms_1122_);
lean_dec(v___x_1121_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1201_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___y_1129_; lean_object* v___y_1138_; lean_object* v_i_1139_; lean_object* v___y_1155_; lean_object* v_i_1156_; lean_object* v___y_1162_; lean_object* v___x_1171_; 
v___x_1171_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v_evalsAtCache_1124_, v_originalExpr_1112_);
switch(lean_obj_tag(v___x_1171_))
{
case 0:
{
lean_object* v_index_1172_; lean_object* v_size_1173_; lean_object* v___x_1174_; 
v_index_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_index_1172_);
lean_dec_ref_known(v___x_1171_, 3);
v_size_1173_ = lean_ctor_get(v_evalsAtCache_1124_, 0);
lean_inc(v_size_1173_);
lean_inc(v_a_1117_);
v___x_1174_ = l_Std_DHashMap_Raw_setEntry___redArg(v_evalsAtCache_1124_, v_size_1173_, v_index_1172_, v_originalExpr_1112_, v_a_1117_);
lean_dec(v_index_1172_);
v___y_1129_ = v___x_1174_;
goto v___jp_1128_;
}
case 1:
{
lean_object* v_index_1175_; lean_object* v_size_1176_; lean_object* v_keyArray_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; 
v_index_1175_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_index_1175_);
lean_dec_ref_known(v___x_1171_, 1);
v_size_1176_ = lean_ctor_get(v_evalsAtCache_1124_, 0);
v_keyArray_1177_ = lean_ctor_get(v_evalsAtCache_1124_, 1);
v___x_1178_ = lean_unsigned_to_nat(1u);
v___x_1179_ = lean_nat_add(v_size_1176_, v___x_1178_);
v___x_1180_ = lean_array_get_size(v_keyArray_1177_);
v___x_1181_ = lean_nat_dec_lt(v___x_1179_, v___x_1180_);
if (v___x_1181_ == 0)
{
lean_dec(v___x_1179_);
lean_dec(v_index_1175_);
goto v___jp_1144_;
}
else
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; 
v___x_1182_ = lean_unsigned_to_nat(4u);
v___x_1183_ = lean_nat_mul(v___x_1179_, v___x_1182_);
v___x_1184_ = lean_unsigned_to_nat(3u);
v___x_1185_ = lean_nat_mul(v___x_1180_, v___x_1184_);
v___x_1186_ = lean_nat_dec_le(v___x_1183_, v___x_1185_);
lean_dec(v___x_1185_);
lean_dec(v___x_1183_);
if (v___x_1186_ == 0)
{
lean_dec(v___x_1179_);
lean_dec(v_index_1175_);
goto v___jp_1144_;
}
else
{
lean_object* v___x_1187_; 
lean_inc(v_a_1117_);
v___x_1187_ = l_Std_DHashMap_Raw_setEntry___redArg(v_evalsAtCache_1124_, v___x_1179_, v_index_1175_, v_originalExpr_1112_, v_a_1117_);
lean_dec(v_index_1175_);
v___y_1129_ = v___x_1187_;
goto v___jp_1128_;
}
}
}
default: 
{
lean_object* v_size_1188_; lean_object* v_keyArray_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; 
v_size_1188_ = lean_ctor_get(v_evalsAtCache_1124_, 0);
v_keyArray_1189_ = lean_ctor_get(v_evalsAtCache_1124_, 1);
v___x_1190_ = lean_unsigned_to_nat(1u);
v___x_1191_ = lean_nat_add(v_size_1188_, v___x_1190_);
v___x_1192_ = lean_array_get_size(v_keyArray_1189_);
v___x_1193_ = lean_nat_dec_lt(v___x_1191_, v___x_1192_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; 
lean_dec(v___x_1191_);
v___x_1194_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2___redArg(v_evalsAtCache_1124_);
lean_dec_ref(v_evalsAtCache_1124_);
v___y_1162_ = v___x_1194_;
goto v___jp_1161_;
}
else
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; 
v___x_1195_ = lean_unsigned_to_nat(4u);
v___x_1196_ = lean_nat_mul(v___x_1191_, v___x_1195_);
lean_dec(v___x_1191_);
v___x_1197_ = lean_unsigned_to_nat(3u);
v___x_1198_ = lean_nat_mul(v___x_1192_, v___x_1197_);
v___x_1199_ = lean_nat_dec_le(v___x_1196_, v___x_1198_);
lean_dec(v___x_1198_);
lean_dec(v___x_1196_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; 
v___x_1200_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2___redArg(v_evalsAtCache_1124_);
lean_dec_ref(v_evalsAtCache_1124_);
v___y_1162_ = v___x_1200_;
goto v___jp_1161_;
}
else
{
v___y_1162_ = v_evalsAtCache_1124_;
goto v___jp_1161_;
}
}
}
}
v___jp_1128_:
{
lean_object* v___x_1131_; 
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 2, v___y_1129_);
v___x_1131_ = v___x_1126_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_atoms_1122_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v_atomsAssignmentCache_1123_);
lean_ctor_set(v_reuseFailAlloc_1136_, 2, v___y_1129_);
v___x_1131_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1132_ = lean_st_ref_put(v_a_1103_, v___x_1131_);
if (v_isShared_1120_ == 0)
{
v___x_1134_ = v___x_1119_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1117_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
v___jp_1137_:
{
lean_object* v_size_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v_size_1140_ = lean_ctor_get(v___y_1138_, 0);
v___x_1141_ = lean_unsigned_to_nat(1u);
v___x_1142_ = lean_nat_add(v_size_1140_, v___x_1141_);
lean_inc(v_a_1117_);
v___x_1143_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1138_, v___x_1142_, v_i_1139_, v_originalExpr_1112_, v_a_1117_);
lean_dec(v_i_1139_);
v___y_1129_ = v___x_1143_;
goto v___jp_1128_;
}
v___jp_1144_:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2___redArg(v_evalsAtCache_1124_);
lean_dec_ref(v_evalsAtCache_1124_);
v___x_1146_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v___x_1145_, v_originalExpr_1112_);
switch(lean_obj_tag(v___x_1146_))
{
case 0:
{
lean_object* v_index_1147_; lean_object* v_size_1148_; lean_object* v___x_1149_; 
v_index_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_index_1147_);
lean_dec_ref_known(v___x_1146_, 3);
v_size_1148_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_size_1148_);
lean_inc(v_a_1117_);
v___x_1149_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1145_, v_size_1148_, v_index_1147_, v_originalExpr_1112_, v_a_1117_);
lean_dec(v_index_1147_);
v___y_1129_ = v___x_1149_;
goto v___jp_1128_;
}
case 1:
{
lean_object* v_index_1150_; 
v_index_1150_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_index_1150_);
lean_dec_ref_known(v___x_1146_, 1);
v___y_1138_ = v___x_1145_;
v_i_1139_ = v_index_1150_;
goto v___jp_1137_;
}
default: 
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = lean_unsigned_to_nat(0u);
v___x_1152_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1145_, v___x_1151_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_index_1153_; 
v_index_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc(v_index_1153_);
lean_dec_ref_known(v___x_1152_, 1);
v___y_1138_ = v___x_1145_;
v_i_1139_ = v_index_1153_;
goto v___jp_1137_;
}
else
{
lean_dec_ref(v_originalExpr_1112_);
v___y_1129_ = v___x_1145_;
goto v___jp_1128_;
}
}
}
}
v___jp_1154_:
{
lean_object* v_size_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v_size_1157_ = lean_ctor_get(v___y_1155_, 0);
v___x_1158_ = lean_unsigned_to_nat(1u);
v___x_1159_ = lean_nat_add(v_size_1157_, v___x_1158_);
lean_inc(v_a_1117_);
v___x_1160_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1155_, v___x_1159_, v_i_1156_, v_originalExpr_1112_, v_a_1117_);
lean_dec(v_i_1156_);
v___y_1129_ = v___x_1160_;
goto v___jp_1128_;
}
v___jp_1161_:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v___y_1162_, v_originalExpr_1112_);
switch(lean_obj_tag(v___x_1163_))
{
case 0:
{
lean_object* v_index_1164_; lean_object* v_size_1165_; lean_object* v___x_1166_; 
v_index_1164_ = lean_ctor_get(v___x_1163_, 0);
lean_inc(v_index_1164_);
lean_dec_ref_known(v___x_1163_, 3);
v_size_1165_ = lean_ctor_get(v___y_1162_, 0);
lean_inc(v_size_1165_);
lean_inc(v_a_1117_);
v___x_1166_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1162_, v_size_1165_, v_index_1164_, v_originalExpr_1112_, v_a_1117_);
lean_dec(v_index_1164_);
v___y_1129_ = v___x_1166_;
goto v___jp_1128_;
}
case 1:
{
lean_object* v_index_1167_; 
v_index_1167_ = lean_ctor_get(v___x_1163_, 0);
lean_inc(v_index_1167_);
lean_dec_ref_known(v___x_1163_, 1);
v___y_1155_ = v___y_1162_;
v_i_1156_ = v_index_1167_;
goto v___jp_1154_;
}
default: 
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = lean_unsigned_to_nat(0u);
v___x_1169_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1162_, v___x_1168_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_index_1170_; 
v_index_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_index_1170_);
lean_dec_ref_known(v___x_1169_, 1);
v___y_1155_ = v___y_1162_;
v_i_1156_ = v_index_1170_;
goto v___jp_1154_;
}
else
{
lean_dec_ref(v_originalExpr_1112_);
v___y_1129_ = v___y_1162_;
goto v___jp_1128_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_originalExpr_1112_);
return v___x_1116_;
}
}
else
{
lean_object* v_val_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_dec_ref(v_evalsAtAtoms_x27_1113_);
lean_dec_ref(v_originalExpr_1112_);
v_val_1203_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1115_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_val_1203_);
lean_dec(v___x_1115_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
lean_ctor_set_tag(v___x_1205_, 0);
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_val_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_evalsAtAtoms___boxed(lean_object* v_reified_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_evalsAtAtoms(v_reified_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
lean_dec(v_a_1215_);
lean_dec_ref(v_a_1214_);
lean_dec(v_a_1213_);
lean_dec_ref(v_a_1212_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(lean_object* v_reified_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_){
_start:
{
lean_object* v___x_1232_; lean_object* v_originalExpr_1233_; lean_object* v_evalsAtAtoms_x27_1234_; lean_object* v_evalsAtCache_1235_; lean_object* v___x_1236_; 
v___x_1232_ = lean_st_ref_get(v_a_1224_);
v_originalExpr_1233_ = lean_ctor_get(v_reified_1222_, 1);
lean_inc_ref(v_originalExpr_1233_);
v_evalsAtAtoms_x27_1234_ = lean_ctor_get(v_reified_1222_, 2);
lean_inc_ref(v_evalsAtAtoms_x27_1234_);
lean_dec_ref(v_reified_1222_);
v_evalsAtCache_1235_ = lean_ctor_get(v___x_1232_, 2);
lean_inc_ref(v_evalsAtCache_1235_);
lean_dec(v___x_1232_);
v___x_1236_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_evalsAtCache_1235_, v_originalExpr_1233_);
lean_dec_ref(v_evalsAtCache_1235_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v___x_1237_; 
lean_inc(v_a_1230_);
lean_inc_ref(v_a_1229_);
lean_inc(v_a_1228_);
lean_inc_ref(v_a_1227_);
lean_inc(v_a_1226_);
lean_inc_ref(v_a_1225_);
lean_inc(v_a_1224_);
lean_inc_ref(v_a_1223_);
v___x_1237_ = lean_apply_9(v_evalsAtAtoms_x27_1234_, v_a_1223_, v_a_1224_, v_a_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, lean_box(0));
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1323_; 
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1240_ = v___x_1237_;
v_isShared_1241_ = v_isSharedCheck_1323_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1237_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1323_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1242_; lean_object* v_atoms_1243_; lean_object* v_atomsAssignmentCache_1244_; lean_object* v_evalsAtCache_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1322_; 
v___x_1242_ = lean_st_ref_take(v_a_1224_);
v_atoms_1243_ = lean_ctor_get(v___x_1242_, 0);
v_atomsAssignmentCache_1244_ = lean_ctor_get(v___x_1242_, 1);
v_evalsAtCache_1245_ = lean_ctor_get(v___x_1242_, 2);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1247_ = v___x_1242_;
v_isShared_1248_ = v_isSharedCheck_1322_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_evalsAtCache_1245_);
lean_inc(v_atomsAssignmentCache_1244_);
lean_inc(v_atoms_1243_);
lean_dec(v___x_1242_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1322_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___y_1250_; lean_object* v___y_1259_; lean_object* v_i_1260_; lean_object* v___y_1276_; lean_object* v_i_1277_; lean_object* v___y_1283_; lean_object* v___x_1292_; 
v___x_1292_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v_evalsAtCache_1245_, v_originalExpr_1233_);
switch(lean_obj_tag(v___x_1292_))
{
case 0:
{
lean_object* v_index_1293_; lean_object* v_size_1294_; lean_object* v___x_1295_; 
v_index_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_index_1293_);
lean_dec_ref_known(v___x_1292_, 3);
v_size_1294_ = lean_ctor_get(v_evalsAtCache_1245_, 0);
lean_inc(v_size_1294_);
lean_inc(v_a_1238_);
v___x_1295_ = l_Std_DHashMap_Raw_setEntry___redArg(v_evalsAtCache_1245_, v_size_1294_, v_index_1293_, v_originalExpr_1233_, v_a_1238_);
lean_dec(v_index_1293_);
v___y_1250_ = v___x_1295_;
goto v___jp_1249_;
}
case 1:
{
lean_object* v_index_1296_; lean_object* v_size_1297_; lean_object* v_keyArray_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; uint8_t v___x_1302_; 
v_index_1296_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_index_1296_);
lean_dec_ref_known(v___x_1292_, 1);
v_size_1297_ = lean_ctor_get(v_evalsAtCache_1245_, 0);
v_keyArray_1298_ = lean_ctor_get(v_evalsAtCache_1245_, 1);
v___x_1299_ = lean_unsigned_to_nat(1u);
v___x_1300_ = lean_nat_add(v_size_1297_, v___x_1299_);
v___x_1301_ = lean_array_get_size(v_keyArray_1298_);
v___x_1302_ = lean_nat_dec_lt(v___x_1300_, v___x_1301_);
if (v___x_1302_ == 0)
{
lean_dec(v___x_1300_);
lean_dec(v_index_1296_);
goto v___jp_1265_;
}
else
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v___x_1303_ = lean_unsigned_to_nat(4u);
v___x_1304_ = lean_nat_mul(v___x_1300_, v___x_1303_);
v___x_1305_ = lean_unsigned_to_nat(3u);
v___x_1306_ = lean_nat_mul(v___x_1301_, v___x_1305_);
v___x_1307_ = lean_nat_dec_le(v___x_1304_, v___x_1306_);
lean_dec(v___x_1306_);
lean_dec(v___x_1304_);
if (v___x_1307_ == 0)
{
lean_dec(v___x_1300_);
lean_dec(v_index_1296_);
goto v___jp_1265_;
}
else
{
lean_object* v___x_1308_; 
lean_inc(v_a_1238_);
v___x_1308_ = l_Std_DHashMap_Raw_setEntry___redArg(v_evalsAtCache_1245_, v___x_1300_, v_index_1296_, v_originalExpr_1233_, v_a_1238_);
lean_dec(v_index_1296_);
v___y_1250_ = v___x_1308_;
goto v___jp_1249_;
}
}
}
default: 
{
lean_object* v_size_1309_; lean_object* v_keyArray_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v_size_1309_ = lean_ctor_get(v_evalsAtCache_1245_, 0);
v_keyArray_1310_ = lean_ctor_get(v_evalsAtCache_1245_, 1);
v___x_1311_ = lean_unsigned_to_nat(1u);
v___x_1312_ = lean_nat_add(v_size_1309_, v___x_1311_);
v___x_1313_ = lean_array_get_size(v_keyArray_1310_);
v___x_1314_ = lean_nat_dec_lt(v___x_1312_, v___x_1313_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; 
lean_dec(v___x_1312_);
v___x_1315_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2___redArg(v_evalsAtCache_1245_);
lean_dec_ref(v_evalsAtCache_1245_);
v___y_1283_ = v___x_1315_;
goto v___jp_1282_;
}
else
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; uint8_t v___x_1320_; 
v___x_1316_ = lean_unsigned_to_nat(4u);
v___x_1317_ = lean_nat_mul(v___x_1312_, v___x_1316_);
lean_dec(v___x_1312_);
v___x_1318_ = lean_unsigned_to_nat(3u);
v___x_1319_ = lean_nat_mul(v___x_1313_, v___x_1318_);
v___x_1320_ = lean_nat_dec_le(v___x_1317_, v___x_1319_);
lean_dec(v___x_1319_);
lean_dec(v___x_1317_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; 
v___x_1321_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2___redArg(v_evalsAtCache_1245_);
lean_dec_ref(v_evalsAtCache_1245_);
v___y_1283_ = v___x_1321_;
goto v___jp_1282_;
}
else
{
v___y_1283_ = v_evalsAtCache_1245_;
goto v___jp_1282_;
}
}
}
}
v___jp_1249_:
{
lean_object* v___x_1252_; 
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 2, v___y_1250_);
v___x_1252_ = v___x_1247_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_atoms_1243_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_atomsAssignmentCache_1244_);
lean_ctor_set(v_reuseFailAlloc_1257_, 2, v___y_1250_);
v___x_1252_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
lean_object* v___x_1253_; lean_object* v___x_1255_; 
v___x_1253_ = lean_st_ref_put(v_a_1224_, v___x_1252_);
if (v_isShared_1241_ == 0)
{
v___x_1255_ = v___x_1240_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1238_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
v___jp_1258_:
{
lean_object* v_size_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v_size_1261_ = lean_ctor_get(v___y_1259_, 0);
v___x_1262_ = lean_unsigned_to_nat(1u);
v___x_1263_ = lean_nat_add(v_size_1261_, v___x_1262_);
lean_inc(v_a_1238_);
v___x_1264_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1259_, v___x_1263_, v_i_1260_, v_originalExpr_1233_, v_a_1238_);
lean_dec(v_i_1260_);
v___y_1250_ = v___x_1264_;
goto v___jp_1249_;
}
v___jp_1265_:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2___redArg(v_evalsAtCache_1245_);
lean_dec_ref(v_evalsAtCache_1245_);
v___x_1267_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v___x_1266_, v_originalExpr_1233_);
switch(lean_obj_tag(v___x_1267_))
{
case 0:
{
lean_object* v_index_1268_; lean_object* v_size_1269_; lean_object* v___x_1270_; 
v_index_1268_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_index_1268_);
lean_dec_ref_known(v___x_1267_, 3);
v_size_1269_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_size_1269_);
lean_inc(v_a_1238_);
v___x_1270_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1266_, v_size_1269_, v_index_1268_, v_originalExpr_1233_, v_a_1238_);
lean_dec(v_index_1268_);
v___y_1250_ = v___x_1270_;
goto v___jp_1249_;
}
case 1:
{
lean_object* v_index_1271_; 
v_index_1271_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_index_1271_);
lean_dec_ref_known(v___x_1267_, 1);
v___y_1259_ = v___x_1266_;
v_i_1260_ = v_index_1271_;
goto v___jp_1258_;
}
default: 
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = lean_unsigned_to_nat(0u);
v___x_1273_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1266_, v___x_1272_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_index_1274_; 
v_index_1274_ = lean_ctor_get(v___x_1273_, 0);
lean_inc(v_index_1274_);
lean_dec_ref_known(v___x_1273_, 1);
v___y_1259_ = v___x_1266_;
v_i_1260_ = v_index_1274_;
goto v___jp_1258_;
}
else
{
lean_dec_ref(v_originalExpr_1233_);
v___y_1250_ = v___x_1266_;
goto v___jp_1249_;
}
}
}
}
v___jp_1275_:
{
lean_object* v_size_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v_size_1278_ = lean_ctor_get(v___y_1276_, 0);
v___x_1279_ = lean_unsigned_to_nat(1u);
v___x_1280_ = lean_nat_add(v_size_1278_, v___x_1279_);
lean_inc(v_a_1238_);
v___x_1281_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1276_, v___x_1280_, v_i_1277_, v_originalExpr_1233_, v_a_1238_);
lean_dec(v_i_1277_);
v___y_1250_ = v___x_1281_;
goto v___jp_1249_;
}
v___jp_1282_:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v___y_1283_, v_originalExpr_1233_);
switch(lean_obj_tag(v___x_1284_))
{
case 0:
{
lean_object* v_index_1285_; lean_object* v_size_1286_; lean_object* v___x_1287_; 
v_index_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_index_1285_);
lean_dec_ref_known(v___x_1284_, 3);
v_size_1286_ = lean_ctor_get(v___y_1283_, 0);
lean_inc(v_size_1286_);
lean_inc(v_a_1238_);
v___x_1287_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1283_, v_size_1286_, v_index_1285_, v_originalExpr_1233_, v_a_1238_);
lean_dec(v_index_1285_);
v___y_1250_ = v___x_1287_;
goto v___jp_1249_;
}
case 1:
{
lean_object* v_index_1288_; 
v_index_1288_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_index_1288_);
lean_dec_ref_known(v___x_1284_, 1);
v___y_1276_ = v___y_1283_;
v_i_1277_ = v_index_1288_;
goto v___jp_1275_;
}
default: 
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = lean_unsigned_to_nat(0u);
v___x_1290_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1283_, v___x_1289_);
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_index_1291_; 
v_index_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_index_1291_);
lean_dec_ref_known(v___x_1290_, 1);
v___y_1276_ = v___y_1283_;
v_i_1277_ = v_index_1291_;
goto v___jp_1275_;
}
else
{
lean_dec_ref(v_originalExpr_1233_);
v___y_1250_ = v___y_1283_;
goto v___jp_1249_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_originalExpr_1233_);
return v___x_1237_;
}
}
else
{
lean_object* v_val_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
lean_dec_ref(v_evalsAtAtoms_x27_1234_);
lean_dec_ref(v_originalExpr_1233_);
v_val_1324_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1236_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_val_1324_);
lean_dec(v___x_1236_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
lean_ctor_set_tag(v___x_1326_, 0);
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_val_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms___boxed(lean_object* v_reified_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(v_reified_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
lean_dec(v_a_1340_);
lean_dec_ref(v_a_1339_);
lean_dec(v_a_1338_);
lean_dec_ref(v_a_1337_);
lean_dec(v_a_1336_);
lean_dec_ref(v_a_1335_);
lean_dec(v_a_1334_);
lean_dec_ref(v_a_1333_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_M_run_spec__0(size_t v_sz_1343_, size_t v_i_1344_, lean_object* v_bs_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
uint8_t v___x_1353_; 
v___x_1353_ = lean_usize_dec_lt(v_i_1344_, v_sz_1343_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; 
v___x_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1354_, 0, v_bs_1345_);
return v___x_1354_;
}
else
{
lean_object* v_v_1355_; lean_object* v_name_1356_; lean_object* v_type_1357_; lean_object* v_value_1358_; lean_object* v_source_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1382_; 
v_v_1355_ = lean_array_uget(v_bs_1345_, v_i_1344_);
v_name_1356_ = lean_ctor_get(v_v_1355_, 0);
v_type_1357_ = lean_ctor_get(v_v_1355_, 1);
v_value_1358_ = lean_ctor_get(v_v_1355_, 2);
v_source_1359_ = lean_ctor_get(v_v_1355_, 3);
v_isSharedCheck_1382_ = !lean_is_exclusive(v_v_1355_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1361_ = v_v_1355_;
v_isShared_1362_ = v_isSharedCheck_1382_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_source_1359_);
lean_inc(v_value_1358_);
lean_inc(v_type_1357_);
lean_inc(v_name_1356_);
lean_dec(v_v_1355_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1382_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; 
v___x_1363_ = l_Lean_Meta_Sym_shareCommon(v_type_1357_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v___x_1365_; lean_object* v_bs_x27_1366_; lean_object* v___x_1368_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1364_);
lean_dec_ref_known(v___x_1363_, 1);
v___x_1365_ = lean_unsigned_to_nat(0u);
v_bs_x27_1366_ = lean_array_uset(v_bs_1345_, v_i_1344_, v___x_1365_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 1, v_a_1364_);
v___x_1368_ = v___x_1361_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_name_1356_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_a_1364_);
lean_ctor_set(v_reuseFailAlloc_1373_, 2, v_value_1358_);
lean_ctor_set(v_reuseFailAlloc_1373_, 3, v_source_1359_);
v___x_1368_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
size_t v___x_1369_; size_t v___x_1370_; lean_object* v___x_1371_; 
v___x_1369_ = ((size_t)1ULL);
v___x_1370_ = lean_usize_add(v_i_1344_, v___x_1369_);
v___x_1371_ = lean_array_uset(v_bs_x27_1366_, v_i_1344_, v___x_1368_);
v_i_1344_ = v___x_1370_;
v_bs_1345_ = v___x_1371_;
goto _start;
}
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
lean_del_object(v___x_1361_);
lean_dec(v_source_1359_);
lean_dec_ref(v_value_1358_);
lean_dec(v_name_1356_);
lean_dec_ref(v_bs_1345_);
v_a_1374_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1363_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1363_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1379_; 
if (v_isShared_1377_ == 0)
{
v___x_1379_ = v___x_1376_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_M_run_spec__0___boxed(lean_object* v_sz_1383_, lean_object* v_i_1384_, lean_object* v_bs_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
size_t v_sz_boxed_1393_; size_t v_i_boxed_1394_; lean_object* v_res_1395_; 
v_sz_boxed_1393_ = lean_unbox_usize(v_sz_1383_);
lean_dec(v_sz_1383_);
v_i_boxed_1394_ = lean_unbox_usize(v_i_1384_);
lean_dec(v_i_1384_);
v_res_1395_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_M_run_spec__0(v_sz_boxed_1393_, v_i_boxed_1394_, v_bs_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
return v_res_1395_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__0(void){
_start:
{
lean_object* v_cellCount_1396_; lean_object* v___x_1397_; 
v_cellCount_1396_ = lean_unsigned_to_nat(16u);
v___x_1397_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1396_);
return v___x_1397_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__1(void){
_start:
{
lean_object* v_cellCount_1398_; lean_object* v___x_1399_; 
v_cellCount_1398_ = lean_unsigned_to_nat(16u);
v___x_1399_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1398_);
return v___x_1399_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1400_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__1);
v___x_1401_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__0);
v___x_1402_ = lean_unsigned_to_nat(0u);
v___x_1403_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1402_);
lean_ctor_set(v___x_1403_, 1, v___x_1401_);
lean_ctor_set(v___x_1403_, 2, v___x_1400_);
return v___x_1403_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__3(void){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1404_ = lean_box(0);
v___x_1405_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__2, &l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__2);
v___x_1406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
lean_ctor_set(v___x_1406_, 1, v___x_1404_);
lean_ctor_set(v___x_1406_, 2, v___x_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_run___redArg(lean_object* v_m_1407_, lean_object* v_hypotheses_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_){
_start:
{
size_t v_sz_1416_; size_t v___x_1417_; lean_object* v___x_1418_; 
v_sz_1416_ = lean_array_size(v_hypotheses_1408_);
v___x_1417_ = ((size_t)0ULL);
v___x_1418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_M_run_spec__0(v_sz_1416_, v___x_1417_, v_hypotheses_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_);
if (lean_obj_tag(v___x_1418_) == 0)
{
lean_object* v_a_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1419_);
lean_dec_ref_known(v___x_1418_, 1);
v___x_1420_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__3);
v___x_1421_ = lean_st_mk_ref(v___x_1420_);
lean_inc(v_a_1414_);
lean_inc_ref(v_a_1413_);
lean_inc(v_a_1412_);
lean_inc_ref(v_a_1411_);
lean_inc(v_a_1410_);
lean_inc_ref(v_a_1409_);
lean_inc(v___x_1421_);
v___x_1422_ = lean_apply_9(v_m_1407_, v_a_1419_, v___x_1421_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, lean_box(0));
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1431_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1425_ = v___x_1422_;
v_isShared_1426_ = v_isSharedCheck_1431_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1422_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1431_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v___x_1427_; lean_object* v___x_1429_; 
v___x_1427_ = lean_st_ref_get(v___x_1421_);
lean_dec(v___x_1421_);
lean_dec(v___x_1427_);
if (v_isShared_1426_ == 0)
{
v___x_1429_ = v___x_1425_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_a_1423_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
else
{
lean_dec(v___x_1421_);
return v___x_1422_;
}
}
else
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
lean_dec_ref(v_m_1407_);
v_a_1432_ = lean_ctor_get(v___x_1418_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1418_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v___x_1418_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1418_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_run___redArg___boxed(lean_object* v_m_1440_, lean_object* v_hypotheses_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lean_Meta_Tactic_BVDecide_M_run___redArg(v_m_1440_, v_hypotheses_1441_, v_a_1442_, v_a_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
lean_dec(v_a_1445_);
lean_dec_ref(v_a_1444_);
lean_dec(v_a_1443_);
lean_dec_ref(v_a_1442_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_run(lean_object* v_00_u03b1_1450_, lean_object* v_m_1451_, lean_object* v_hypotheses_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_){
_start:
{
lean_object* v___x_1460_; 
v___x_1460_ = l_Lean_Meta_Tactic_BVDecide_M_run___redArg(v_m_1451_, v_hypotheses_1452_, v_a_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_, v_a_1458_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_run___boxed(lean_object* v_00_u03b1_1461_, lean_object* v_m_1462_, lean_object* v_hypotheses_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Lean_Meta_Tactic_BVDecide_M_run(v_00_u03b1_1461_, v_m_1462_, v_hypotheses_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
lean_dec(v_a_1469_);
lean_dec_ref(v_a_1468_);
lean_dec(v_a_1467_);
lean_dec_ref(v_a_1466_);
lean_dec(v_a_1465_);
lean_dec_ref(v_a_1464_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2_spec__3___redArg(lean_object* v_hi_1472_, lean_object* v_pivot_1473_, lean_object* v_as_1474_, lean_object* v_i_1475_, lean_object* v_k_1476_){
_start:
{
uint8_t v___x_1477_; 
v___x_1477_ = lean_nat_dec_lt(v_k_1476_, v_hi_1472_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
lean_dec(v_k_1476_);
v___x_1478_ = lean_array_fswap(v_as_1474_, v_i_1475_, v_hi_1472_);
v___x_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1479_, 0, v_i_1475_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
return v___x_1479_;
}
else
{
lean_object* v___x_1480_; lean_object* v_snd_1481_; lean_object* v_snd_1482_; lean_object* v_atomNumber_1483_; lean_object* v_atomNumber_1484_; uint8_t v___x_1485_; 
v___x_1480_ = lean_array_fget_borrowed(v_as_1474_, v_k_1476_);
v_snd_1481_ = lean_ctor_get(v___x_1480_, 1);
v_snd_1482_ = lean_ctor_get(v_pivot_1473_, 1);
v_atomNumber_1483_ = lean_ctor_get(v_snd_1481_, 1);
v_atomNumber_1484_ = lean_ctor_get(v_snd_1482_, 1);
v___x_1485_ = lean_nat_dec_lt(v_atomNumber_1483_, v_atomNumber_1484_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = lean_unsigned_to_nat(1u);
v___x_1487_ = lean_nat_add(v_k_1476_, v___x_1486_);
lean_dec(v_k_1476_);
v_k_1476_ = v___x_1487_;
goto _start;
}
else
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1489_ = lean_array_fswap(v_as_1474_, v_i_1475_, v_k_1476_);
v___x_1490_ = lean_unsigned_to_nat(1u);
v___x_1491_ = lean_nat_add(v_i_1475_, v___x_1490_);
lean_dec(v_i_1475_);
v___x_1492_ = lean_nat_add(v_k_1476_, v___x_1490_);
lean_dec(v_k_1476_);
v_as_1474_ = v___x_1489_;
v_i_1475_ = v___x_1491_;
v_k_1476_ = v___x_1492_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2_spec__3___redArg___boxed(lean_object* v_hi_1494_, lean_object* v_pivot_1495_, lean_object* v_as_1496_, lean_object* v_i_1497_, lean_object* v_k_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2_spec__3___redArg(v_hi_1494_, v_pivot_1495_, v_as_1496_, v_i_1497_, v_k_1498_);
lean_dec_ref(v_pivot_1495_);
lean_dec(v_hi_1494_);
return v_res_1499_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2___redArg___lam__0(lean_object* v_x1_1500_, lean_object* v_x2_1501_){
_start:
{
lean_object* v_snd_1502_; lean_object* v_snd_1503_; lean_object* v_atomNumber_1504_; lean_object* v_atomNumber_1505_; uint8_t v___x_1506_; 
v_snd_1502_ = lean_ctor_get(v_x1_1500_, 1);
v_snd_1503_ = lean_ctor_get(v_x2_1501_, 1);
v_atomNumber_1504_ = lean_ctor_get(v_snd_1502_, 1);
v_atomNumber_1505_ = lean_ctor_get(v_snd_1503_, 1);
v___x_1506_ = lean_nat_dec_lt(v_atomNumber_1504_, v_atomNumber_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2___redArg___lam__0___boxed(lean_object* v_x1_1507_, lean_object* v_x2_1508_){
_start:
{
uint8_t v_res_1509_; lean_object* v_r_1510_; 
v_res_1509_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2___redArg___lam__0(v_x1_1507_, v_x2_1508_);
lean_dec_ref(v_x2_1508_);
lean_dec_ref(v_x1_1507_);
v_r_1510_ = lean_box(v_res_1509_);
return v_r_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2___redArg(lean_object* v_n_1511_, lean_object* v_as_1512_, lean_object* v_lo_1513_, lean_object* v_hi_1514_){
_start:
{
lean_object* v___y_1516_; uint8_t v___x_1526_; 
v___x_1526_ = lean_nat_dec_lt(v_lo_1513_, v_hi_1514_);
if (v___x_1526_ == 0)
{
lean_dec(v_lo_1513_);
return v_as_1512_;
}
else
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v_mid_1529_; lean_object* v___y_1531_; lean_object* v___y_1537_; lean_object* v___x_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; 
v___x_1527_ = lean_nat_add(v_lo_1513_, v_hi_1514_);
v___x_1528_ = lean_unsigned_to_nat(1u);
v_mid_1529_ = lean_nat_shiftr(v___x_1527_, v___x_1528_);
lean_dec(v___x_1527_);
v___x_1542_ = lean_array_fget_borrowed(v_as_1512_, v_mid_1529_);
v___x_1543_ = lean_array_fget_borrowed(v_as_1512_, v_lo_1513_);
v___x_1544_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2___redArg___lam__0(v___x_1542_, v___x_1543_);
if (v___x_1544_ == 0)
{
v___y_1537_ = v_as_1512_;
goto v___jp_1536_;
}
else
{
lean_object* v___x_1545_; 
v___x_1545_ = lean_array_fswap(v_as_1512_, v_lo_1513_, v_mid_1529_);
v___y_1537_ = v___x_1545_;
goto v___jp_1536_;
}
v___jp_1530_:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; 
v___x_1532_ = lean_array_fget_borrowed(v___y_1531_, v_mid_1529_);
v___x_1533_ = lean_array_fget_borrowed(v___y_1531_, v_hi_1514_);
v___x_1534_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2___redArg___lam__0(v___x_1532_, v___x_1533_);
if (v___x_1534_ == 0)
{
lean_dec(v_mid_1529_);
v___y_1516_ = v___y_1531_;
goto v___jp_1515_;
}
else
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_array_fswap(v___y_1531_, v_mid_1529_, v_hi_1514_);
lean_dec(v_mid_1529_);
v___y_1516_ = v___x_1535_;
goto v___jp_1515_;
}
}
v___jp_1536_:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; 
v___x_1538_ = lean_array_fget_borrowed(v___y_1537_, v_hi_1514_);
v___x_1539_ = lean_array_fget_borrowed(v___y_1537_, v_lo_1513_);
v___x_1540_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2___redArg___lam__0(v___x_1538_, v___x_1539_);
if (v___x_1540_ == 0)
{
v___y_1531_ = v___y_1537_;
goto v___jp_1530_;
}
else
{
lean_object* v___x_1541_; 
v___x_1541_ = lean_array_fswap(v___y_1537_, v_lo_1513_, v_hi_1514_);
v___y_1531_ = v___x_1541_;
goto v___jp_1530_;
}
}
}
v___jp_1515_:
{
lean_object* v_pivot_1517_; lean_object* v___x_1518_; lean_object* v_fst_1519_; lean_object* v_snd_1520_; uint8_t v___x_1521_; 
v_pivot_1517_ = lean_array_fget(v___y_1516_, v_hi_1514_);
lean_inc_n(v_lo_1513_, 2);
v___x_1518_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2_spec__3___redArg(v_hi_1514_, v_pivot_1517_, v___y_1516_, v_lo_1513_, v_lo_1513_);
lean_dec(v_pivot_1517_);
v_fst_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_fst_1519_);
v_snd_1520_ = lean_ctor_get(v___x_1518_, 1);
lean_inc(v_snd_1520_);
lean_dec_ref(v___x_1518_);
v___x_1521_ = lean_nat_dec_le(v_hi_1514_, v_fst_1519_);
if (v___x_1521_ == 0)
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1522_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2___redArg(v_n_1511_, v_snd_1520_, v_lo_1513_, v_fst_1519_);
v___x_1523_ = lean_unsigned_to_nat(1u);
v___x_1524_ = lean_nat_add(v_fst_1519_, v___x_1523_);
lean_dec(v_fst_1519_);
v_as_1512_ = v___x_1522_;
v_lo_1513_ = v___x_1524_;
goto _start;
}
else
{
lean_dec(v_fst_1519_);
lean_dec(v_lo_1513_);
return v_snd_1520_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2___redArg___boxed(lean_object* v_n_1546_, lean_object* v_as_1547_, lean_object* v_lo_1548_, lean_object* v_hi_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2___redArg(v_n_1546_, v_as_1547_, v_lo_1548_, v_hi_1549_);
lean_dec(v_hi_1549_);
lean_dec(v_n_1546_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__0(size_t v_sz_1551_, size_t v_i_1552_, lean_object* v_bs_1553_){
_start:
{
uint8_t v___x_1554_; 
v___x_1554_ = lean_usize_dec_lt(v_i_1552_, v_sz_1551_);
if (v___x_1554_ == 0)
{
return v_bs_1553_;
}
else
{
lean_object* v_v_1555_; lean_object* v_snd_1556_; lean_object* v_fst_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1571_; 
v_v_1555_ = lean_array_uget(v_bs_1553_, v_i_1552_);
v_snd_1556_ = lean_ctor_get(v_v_1555_, 1);
v_fst_1557_ = lean_ctor_get(v_v_1555_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_v_1555_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1559_ = v_v_1555_;
v_isShared_1560_ = v_isSharedCheck_1571_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_snd_1556_);
lean_inc(v_fst_1557_);
lean_dec(v_v_1555_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1571_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v_width_1561_; lean_object* v___x_1562_; lean_object* v_bs_x27_1563_; lean_object* v___x_1565_; 
v_width_1561_ = lean_ctor_get(v_snd_1556_, 0);
lean_inc(v_width_1561_);
lean_dec(v_snd_1556_);
v___x_1562_ = lean_unsigned_to_nat(0u);
v_bs_x27_1563_ = lean_array_uset(v_bs_1553_, v_i_1552_, v___x_1562_);
if (v_isShared_1560_ == 0)
{
lean_ctor_set(v___x_1559_, 1, v_fst_1557_);
lean_ctor_set(v___x_1559_, 0, v_width_1561_);
v___x_1565_ = v___x_1559_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_width_1561_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_fst_1557_);
v___x_1565_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
size_t v___x_1566_; size_t v___x_1567_; lean_object* v___x_1568_; 
v___x_1566_ = ((size_t)1ULL);
v___x_1567_ = lean_usize_add(v_i_1552_, v___x_1566_);
v___x_1568_ = lean_array_uset(v_bs_x27_1563_, v_i_1552_, v___x_1565_);
v_i_1552_ = v___x_1567_;
v_bs_1553_ = v___x_1568_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__0___boxed(lean_object* v_sz_1572_, lean_object* v_i_1573_, lean_object* v_bs_1574_){
_start:
{
size_t v_sz_boxed_1575_; size_t v_i_boxed_1576_; lean_object* v_res_1577_; 
v_sz_boxed_1575_ = lean_unbox_usize(v_sz_1572_);
lean_dec(v_sz_1572_);
v_i_boxed_1576_ = lean_unbox_usize(v_i_1573_);
lean_dec(v_i_1573_);
v_res_1577_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__0(v_sz_boxed_1575_, v_i_boxed_1576_, v_bs_1574_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1_spec__1(lean_object* v_b_1578_, lean_object* v_acc_1579_, lean_object* v_i_1580_){
_start:
{
lean_object* v_keyArray_1585_; lean_object* v_valueArray_1586_; lean_object* v___x_1587_; uint8_t v___x_1588_; 
v_keyArray_1585_ = lean_ctor_get(v_b_1578_, 1);
v_valueArray_1586_ = lean_ctor_get(v_b_1578_, 2);
v___x_1587_ = lean_array_get_size(v_keyArray_1585_);
v___x_1588_ = lean_nat_dec_lt(v_i_1580_, v___x_1587_);
if (v___x_1588_ == 0)
{
lean_dec(v_i_1580_);
return v_acc_1579_;
}
else
{
lean_object* v___x_1589_; uint8_t v_isSome_1590_; 
v___x_1589_ = lean_array_fget_borrowed(v_keyArray_1585_, v_i_1580_);
v_isSome_1590_ = lean_noption_is_some(v___x_1589_);
if (v_isSome_1590_ == 0)
{
goto v___jp_1581_;
}
else
{
lean_object* v___x_1591_; uint8_t v_isSome_1592_; 
v___x_1591_ = lean_array_fget_borrowed(v_valueArray_1586_, v_i_1580_);
v_isSome_1592_ = lean_noption_is_some(v___x_1591_);
if (v_isSome_1592_ == 0)
{
goto v___jp_1581_;
}
else
{
lean_object* v_val_1593_; lean_object* v_val_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
lean_inc(v___x_1589_);
v_val_1593_ = lean_noption_get(v___x_1589_);
lean_inc(v___x_1591_);
v_val_1594_ = lean_noption_get(v___x_1591_);
v___x_1595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1595_, 0, v_val_1593_);
lean_ctor_set(v___x_1595_, 1, v_val_1594_);
v___x_1596_ = lean_array_push(v_acc_1579_, v___x_1595_);
v___x_1597_ = lean_unsigned_to_nat(1u);
v___x_1598_ = lean_nat_add(v_i_1580_, v___x_1597_);
lean_dec(v_i_1580_);
v_acc_1579_ = v___x_1596_;
v_i_1580_ = v___x_1598_;
goto _start;
}
}
}
v___jp_1581_:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = lean_unsigned_to_nat(1u);
v___x_1583_ = lean_nat_add(v_i_1580_, v___x_1582_);
lean_dec(v_i_1580_);
v_i_1580_ = v___x_1583_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1_spec__1___boxed(lean_object* v_b_1600_, lean_object* v_acc_1601_, lean_object* v_i_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1_spec__1(v_b_1600_, v_acc_1601_, v_i_1602_);
lean_dec_ref(v_b_1600_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1(lean_object* v_init_1604_, lean_object* v_b_1605_){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1606_ = lean_unsigned_to_nat(0u);
v___x_1607_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1_spec__1(v_b_1605_, v_init_1604_, v___x_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1___boxed(lean_object* v_init_1608_, lean_object* v_b_1609_){
_start:
{
lean_object* v_res_1610_; 
v_res_1610_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1(v_init_1608_, v_b_1609_);
lean_dec_ref(v_b_1609_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_atoms___redArg(lean_object* v_a_1611_){
_start:
{
lean_object* v___x_1613_; lean_object* v___y_1615_; lean_object* v_atoms_1620_; lean_object* v_size_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___y_1626_; lean_object* v___y_1627_; lean_object* v___x_1629_; uint8_t v___x_1630_; 
v___x_1613_ = lean_st_ref_get(v_a_1611_);
v_atoms_1620_ = lean_ctor_get(v___x_1613_, 0);
lean_inc_ref(v_atoms_1620_);
lean_dec(v___x_1613_);
v_size_1621_ = lean_ctor_get(v_atoms_1620_, 0);
v___x_1622_ = lean_mk_empty_array_with_capacity(v_size_1621_);
v___x_1623_ = l_Std_DHashMap_Raw_foldM___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__1(v___x_1622_, v_atoms_1620_);
lean_dec_ref(v_atoms_1620_);
v___x_1624_ = lean_array_get_size(v___x_1623_);
v___x_1629_ = lean_unsigned_to_nat(0u);
v___x_1630_ = lean_nat_dec_eq(v___x_1624_, v___x_1629_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___y_1634_; uint8_t v___x_1636_; 
v___x_1631_ = lean_unsigned_to_nat(1u);
v___x_1632_ = lean_nat_sub(v___x_1624_, v___x_1631_);
v___x_1636_ = lean_nat_dec_le(v___x_1629_, v___x_1632_);
if (v___x_1636_ == 0)
{
lean_inc(v___x_1632_);
v___y_1634_ = v___x_1632_;
goto v___jp_1633_;
}
else
{
v___y_1634_ = v___x_1629_;
goto v___jp_1633_;
}
v___jp_1633_:
{
uint8_t v___x_1635_; 
v___x_1635_ = lean_nat_dec_le(v___y_1634_, v___x_1632_);
if (v___x_1635_ == 0)
{
lean_dec(v___x_1632_);
lean_inc(v___y_1634_);
v___y_1626_ = v___y_1634_;
v___y_1627_ = v___y_1634_;
goto v___jp_1625_;
}
else
{
v___y_1626_ = v___y_1634_;
v___y_1627_ = v___x_1632_;
goto v___jp_1625_;
}
}
}
else
{
v___y_1615_ = v___x_1623_;
goto v___jp_1614_;
}
v___jp_1614_:
{
size_t v_sz_1616_; size_t v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v_sz_1616_ = lean_array_size(v___y_1615_);
v___x_1617_ = ((size_t)0ULL);
v___x_1618_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__0(v_sz_1616_, v___x_1617_, v___y_1615_);
v___x_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
return v___x_1619_;
}
v___jp_1625_:
{
lean_object* v___x_1628_; 
v___x_1628_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2___redArg(v___x_1624_, v___x_1623_, v___y_1626_, v___y_1627_);
lean_dec(v___y_1627_);
v___y_1615_ = v___x_1628_;
goto v___jp_1614_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_atoms___redArg___boxed(lean_object* v_a_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_Lean_Meta_Tactic_BVDecide_M_atoms___redArg(v_a_1637_);
lean_dec(v_a_1637_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_atoms(lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Lean_Meta_Tactic_BVDecide_M_atoms___redArg(v_a_1641_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_atoms___boxed(lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_Meta_Tactic_BVDecide_M_atoms(v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_);
lean_dec(v_a_1657_);
lean_dec_ref(v_a_1656_);
lean_dec(v_a_1655_);
lean_dec_ref(v_a_1654_);
lean_dec(v_a_1653_);
lean_dec_ref(v_a_1652_);
lean_dec(v_a_1651_);
lean_dec_ref(v_a_1650_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2(lean_object* v_n_1660_, lean_object* v_as_1661_, lean_object* v_lo_1662_, lean_object* v_hi_1663_, lean_object* v_w_1664_, lean_object* v_hlo_1665_, lean_object* v_hhi_1666_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2___redArg(v_n_1660_, v_as_1661_, v_lo_1662_, v_hi_1663_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2___boxed(lean_object* v_n_1668_, lean_object* v_as_1669_, lean_object* v_lo_1670_, lean_object* v_hi_1671_, lean_object* v_w_1672_, lean_object* v_hlo_1673_, lean_object* v_hhi_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2(v_n_1668_, v_as_1669_, v_lo_1670_, v_hi_1671_, v_w_1672_, v_hlo_1673_, v_hhi_1674_);
lean_dec(v_hi_1671_);
lean_dec(v_n_1668_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2_spec__3(lean_object* v_n_1676_, lean_object* v_lo_1677_, lean_object* v_hi_1678_, lean_object* v_hhi_1679_, lean_object* v_pivot_1680_, lean_object* v_as_1681_, lean_object* v_i_1682_, lean_object* v_k_1683_, lean_object* v_ilo_1684_, lean_object* v_ik_1685_, lean_object* v_w_1686_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2_spec__3___redArg(v_hi_1678_, v_pivot_1680_, v_as_1681_, v_i_1682_, v_k_1683_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2_spec__3___boxed(lean_object* v_n_1688_, lean_object* v_lo_1689_, lean_object* v_hi_1690_, lean_object* v_hhi_1691_, lean_object* v_pivot_1692_, lean_object* v_as_1693_, lean_object* v_i_1694_, lean_object* v_k_1695_, lean_object* v_ilo_1696_, lean_object* v_ik_1697_, lean_object* v_w_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_M_atoms_spec__2_spec__3(v_n_1688_, v_lo_1689_, v_hi_1690_, v_hhi_1691_, v_pivot_1692_, v_as_1693_, v_i_1694_, v_k_1695_, v_ilo_1696_, v_ik_1697_, v_w_1698_);
lean_dec_ref(v_pivot_1692_);
lean_dec(v_hi_1690_);
lean_dec(v_lo_1689_);
lean_dec(v_n_1688_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___lam__0(lean_object* v___x_1701_, lean_object* v___x_1702_, lean_object* v___x_1703_, lean_object* v___x_1704_, lean_object* v___x_1705_, lean_object* v___x_1706_, lean_object* v_x_1707_){
_start:
{
lean_object* v_fst_1708_; lean_object* v_snd_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v_fst_1708_ = lean_ctor_get(v_x_1707_, 0);
lean_inc(v_fst_1708_);
v_snd_1709_ = lean_ctor_get(v_x_1707_, 1);
lean_inc(v_snd_1709_);
lean_dec_ref(v_x_1707_);
v___x_1710_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___lam__0___closed__0));
v___x_1711_ = l_Lean_Name_mkStr6(v___x_1701_, v___x_1702_, v___x_1703_, v___x_1704_, v___x_1705_, v___x_1710_);
v___x_1712_ = l_Lean_mkConst(v___x_1711_, v___x_1706_);
v___x_1713_ = l_Lean_mkNatLit(v_fst_1708_);
v___x_1714_ = l_Lean_mkAppB(v___x_1712_, v___x_1713_, v_snd_1709_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0_spec__0(lean_object* v_msgData_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v___x_1721_; lean_object* v_env_1722_; lean_object* v___x_1723_; lean_object* v_mctx_1724_; lean_object* v_lctx_1725_; lean_object* v_options_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1721_ = lean_st_ref_get(v___y_1719_);
v_env_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc_ref(v_env_1722_);
lean_dec(v___x_1721_);
v___x_1723_ = lean_st_ref_get(v___y_1717_);
v_mctx_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc_ref(v_mctx_1724_);
lean_dec(v___x_1723_);
v_lctx_1725_ = lean_ctor_get(v___y_1716_, 2);
v_options_1726_ = lean_ctor_get(v___y_1718_, 2);
lean_inc_ref(v_options_1726_);
lean_inc_ref(v_lctx_1725_);
v___x_1727_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1727_, 0, v_env_1722_);
lean_ctor_set(v___x_1727_, 1, v_mctx_1724_);
lean_ctor_set(v___x_1727_, 2, v_lctx_1725_);
lean_ctor_set(v___x_1727_, 3, v_options_1726_);
v___x_1728_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1727_);
lean_ctor_set(v___x_1728_, 1, v_msgData_1715_);
v___x_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0_spec__0___boxed(lean_object* v_msgData_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0_spec__0(v_msgData_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0___redArg(lean_object* v_msg_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_ref_1743_; lean_object* v___x_1744_; lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1753_; 
v_ref_1743_ = lean_ctor_get(v___y_1740_, 5);
v___x_1744_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0_spec__0(v_msg_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_);
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1747_ = v___x_1744_;
v_isShared_1748_ = v_isSharedCheck_1753_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1744_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1753_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1749_; lean_object* v___x_1751_; 
lean_inc(v_ref_1743_);
v___x_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1749_, 0, v_ref_1743_);
lean_ctor_set(v___x_1749_, 1, v_a_1745_);
if (v_isShared_1748_ == 0)
{
lean_ctor_set_tag(v___x_1747_, 1);
lean_ctor_set(v___x_1747_, 0, v___x_1749_);
v___x_1751_ = v___x_1747_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1749_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0___redArg___boxed(lean_object* v_msg_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0___redArg(v_msg_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
return v_res_1760_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__1(void){
_start:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__0));
v___x_1763_ = l_Lean_stringToMessageData(v___x_1762_);
return v___x_1763_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__5(void){
_start:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1778_ = lean_box(0);
v___x_1779_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__3));
v___x_1780_ = l_Lean_mkConst(v___x_1779_, v___x_1778_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment(lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v___x_1790_; lean_object* v_a_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; uint8_t v___x_1794_; 
v___x_1790_ = l_Lean_Meta_Tactic_BVDecide_M_atoms___redArg(v_a_1782_);
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_a_1791_);
lean_dec_ref(v___x_1790_);
v___x_1792_ = lean_unsigned_to_nat(0u);
v___x_1793_ = lean_array_get_size(v_a_1791_);
v___x_1794_ = lean_nat_dec_lt(v___x_1792_, v___x_1793_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
lean_dec(v_a_1791_);
v___x_1795_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__1);
v___x_1796_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0___redArg(v___x_1795_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
return v___x_1796_;
}
else
{
lean_object* v___x_1797_; lean_object* v___f_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1797_ = l_Lean_RArray_ofArray___redArg(v_a_1791_);
v___f_1798_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__4));
v___x_1799_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__5, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__5_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___closed__5);
v___x_1800_ = l_Lean_RArray_toExpr___redArg(v___x_1799_, v___f_1798_, v___x_1797_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1829_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1803_ = v___x_1800_;
v_isShared_1804_ = v_isSharedCheck_1829_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_a_1801_);
lean_dec(v___x_1800_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1829_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v___x_1805_; 
v___x_1805_ = l_Lean_Meta_Sym_shareCommon(v_a_1801_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1828_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1808_ = v___x_1805_;
v_isShared_1809_ = v_isSharedCheck_1828_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_a_1806_);
lean_dec(v___x_1805_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1828_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1810_; lean_object* v_atoms_1811_; lean_object* v_evalsAtCache_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1826_; 
v___x_1810_ = lean_st_ref_take(v_a_1782_);
v_atoms_1811_ = lean_ctor_get(v___x_1810_, 0);
v_evalsAtCache_1812_ = lean_ctor_get(v___x_1810_, 2);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1826_ == 0)
{
lean_object* v_unused_1827_; 
v_unused_1827_ = lean_ctor_get(v___x_1810_, 1);
lean_dec(v_unused_1827_);
v___x_1814_ = v___x_1810_;
v_isShared_1815_ = v_isSharedCheck_1826_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_evalsAtCache_1812_);
lean_inc(v_atoms_1811_);
lean_dec(v___x_1810_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1826_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
lean_inc(v_a_1806_);
if (v_isShared_1804_ == 0)
{
lean_ctor_set_tag(v___x_1803_, 1);
lean_ctor_set(v___x_1803_, 0, v_a_1806_);
v___x_1817_ = v___x_1803_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1806_);
v___x_1817_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
lean_object* v___x_1819_; 
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 1, v___x_1817_);
v___x_1819_ = v___x_1814_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_atoms_1811_);
lean_ctor_set(v_reuseFailAlloc_1824_, 1, v___x_1817_);
lean_ctor_set(v_reuseFailAlloc_1824_, 2, v_evalsAtCache_1812_);
v___x_1819_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v___x_1820_; lean_object* v___x_1822_; 
v___x_1820_ = lean_st_ref_put(v_a_1782_, v___x_1819_);
if (v_isShared_1809_ == 0)
{
v___x_1822_ = v___x_1808_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1806_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_1803_);
return v___x_1805_;
}
}
}
else
{
return v___x_1800_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment___boxed(lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment(v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
lean_dec(v_a_1837_);
lean_dec_ref(v_a_1836_);
lean_dec(v_a_1835_);
lean_dec_ref(v_a_1834_);
lean_dec(v_a_1833_);
lean_dec_ref(v_a_1832_);
lean_dec(v_a_1831_);
lean_dec_ref(v_a_1830_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0(lean_object* v_00_u03b1_1840_, lean_object* v_msg_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0___redArg(v_msg_1841_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0___boxed(lean_object* v_00_u03b1_1852_, lean_object* v_msg_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0(v_00_u03b1_1852_, v_msg_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_atomsAssignment(lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_){
_start:
{
lean_object* v___x_1873_; lean_object* v_atomsAssignmentCache_1874_; 
v___x_1873_ = lean_st_ref_get(v_a_1865_);
v_atomsAssignmentCache_1874_ = lean_ctor_get(v___x_1873_, 1);
lean_inc(v_atomsAssignmentCache_1874_);
lean_dec(v___x_1873_);
if (lean_obj_tag(v_atomsAssignmentCache_1874_) == 0)
{
lean_object* v___x_1875_; 
v___x_1875_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment(v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_);
return v___x_1875_;
}
else
{
lean_object* v_val_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1883_; 
v_val_1876_ = lean_ctor_get(v_atomsAssignmentCache_1874_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v_atomsAssignmentCache_1874_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1878_ = v_atomsAssignmentCache_1874_;
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_val_1876_);
lean_dec(v_atomsAssignmentCache_1874_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1883_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1881_; 
if (v_isShared_1879_ == 0)
{
lean_ctor_set_tag(v___x_1878_, 0);
v___x_1881_ = v___x_1878_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_val_1876_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_atomsAssignment___boxed(lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Lean_Meta_Tactic_BVDecide_M_atomsAssignment(v_a_1884_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_);
lean_dec(v_a_1891_);
lean_dec_ref(v_a_1890_);
lean_dec(v_a_1889_);
lean_dec_ref(v_a_1888_);
lean_dec(v_a_1887_);
lean_dec_ref(v_a_1886_);
lean_dec(v_a_1885_);
lean_dec_ref(v_a_1884_);
return v_res_1893_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_instMonadEIO(lean_box(0));
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1(lean_object* v_msg_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v_toApplicative_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1976_; 
v___x_1909_ = lean_obj_once(&l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__0, &l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__0);
v___x_1910_ = l_StateRefT_x27_instMonad___redArg(v___x_1909_);
v_toApplicative_1911_ = lean_ctor_get(v___x_1910_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v___x_1910_);
if (v_isSharedCheck_1976_ == 0)
{
lean_object* v_unused_1977_; 
v_unused_1977_ = lean_ctor_get(v___x_1910_, 1);
lean_dec(v_unused_1977_);
v___x_1913_ = v___x_1910_;
v_isShared_1914_ = v_isSharedCheck_1976_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_toApplicative_1911_);
lean_dec(v___x_1910_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1976_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v_toFunctor_1915_; lean_object* v_toSeq_1916_; lean_object* v_toSeqLeft_1917_; lean_object* v_toSeqRight_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1974_; 
v_toFunctor_1915_ = lean_ctor_get(v_toApplicative_1911_, 0);
v_toSeq_1916_ = lean_ctor_get(v_toApplicative_1911_, 2);
v_toSeqLeft_1917_ = lean_ctor_get(v_toApplicative_1911_, 3);
v_toSeqRight_1918_ = lean_ctor_get(v_toApplicative_1911_, 4);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_toApplicative_1911_);
if (v_isSharedCheck_1974_ == 0)
{
lean_object* v_unused_1975_; 
v_unused_1975_ = lean_ctor_get(v_toApplicative_1911_, 1);
lean_dec(v_unused_1975_);
v___x_1920_ = v_toApplicative_1911_;
v_isShared_1921_ = v_isSharedCheck_1974_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_toSeqRight_1918_);
lean_inc(v_toSeqLeft_1917_);
lean_inc(v_toSeq_1916_);
lean_inc(v_toFunctor_1915_);
lean_dec(v_toApplicative_1911_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1974_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___f_1922_; lean_object* v___f_1923_; lean_object* v___f_1924_; lean_object* v___f_1925_; lean_object* v___x_1926_; lean_object* v___f_1927_; lean_object* v___f_1928_; lean_object* v___f_1929_; lean_object* v___x_1931_; 
v___f_1922_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__1));
v___f_1923_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1915_);
v___f_1924_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1924_, 0, v_toFunctor_1915_);
v___f_1925_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1925_, 0, v_toFunctor_1915_);
v___x_1926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___f_1924_);
lean_ctor_set(v___x_1926_, 1, v___f_1925_);
v___f_1927_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1927_, 0, v_toSeqRight_1918_);
v___f_1928_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1928_, 0, v_toSeqLeft_1917_);
v___f_1929_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1929_, 0, v_toSeq_1916_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 4, v___f_1927_);
lean_ctor_set(v___x_1920_, 3, v___f_1928_);
lean_ctor_set(v___x_1920_, 2, v___f_1929_);
lean_ctor_set(v___x_1920_, 1, v___f_1922_);
lean_ctor_set(v___x_1920_, 0, v___x_1926_);
v___x_1931_ = v___x_1920_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1926_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v___f_1922_);
lean_ctor_set(v_reuseFailAlloc_1973_, 2, v___f_1929_);
lean_ctor_set(v_reuseFailAlloc_1973_, 3, v___f_1928_);
lean_ctor_set(v_reuseFailAlloc_1973_, 4, v___f_1927_);
v___x_1931_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
lean_object* v___x_1933_; 
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 1, v___f_1923_);
lean_ctor_set(v___x_1913_, 0, v___x_1931_);
v___x_1933_ = v___x_1913_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1931_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v___f_1923_);
v___x_1933_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
lean_object* v___x_1934_; lean_object* v_toApplicative_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1970_; 
v___x_1934_ = l_StateRefT_x27_instMonad___redArg(v___x_1933_);
v_toApplicative_1935_ = lean_ctor_get(v___x_1934_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1970_ == 0)
{
lean_object* v_unused_1971_; 
v_unused_1971_ = lean_ctor_get(v___x_1934_, 1);
lean_dec(v_unused_1971_);
v___x_1937_ = v___x_1934_;
v_isShared_1938_ = v_isSharedCheck_1970_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_toApplicative_1935_);
lean_dec(v___x_1934_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1970_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v_toFunctor_1939_; lean_object* v_toSeq_1940_; lean_object* v_toSeqLeft_1941_; lean_object* v_toSeqRight_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1968_; 
v_toFunctor_1939_ = lean_ctor_get(v_toApplicative_1935_, 0);
v_toSeq_1940_ = lean_ctor_get(v_toApplicative_1935_, 2);
v_toSeqLeft_1941_ = lean_ctor_get(v_toApplicative_1935_, 3);
v_toSeqRight_1942_ = lean_ctor_get(v_toApplicative_1935_, 4);
v_isSharedCheck_1968_ = !lean_is_exclusive(v_toApplicative_1935_);
if (v_isSharedCheck_1968_ == 0)
{
lean_object* v_unused_1969_; 
v_unused_1969_ = lean_ctor_get(v_toApplicative_1935_, 1);
lean_dec(v_unused_1969_);
v___x_1944_ = v_toApplicative_1935_;
v_isShared_1945_ = v_isSharedCheck_1968_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_toSeqRight_1942_);
lean_inc(v_toSeqLeft_1941_);
lean_inc(v_toSeq_1940_);
lean_inc(v_toFunctor_1939_);
lean_dec(v_toApplicative_1935_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1968_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___f_1946_; lean_object* v___f_1947_; lean_object* v___f_1948_; lean_object* v___f_1949_; lean_object* v___x_1950_; lean_object* v___f_1951_; lean_object* v___f_1952_; lean_object* v___f_1953_; lean_object* v___x_1955_; 
v___f_1946_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__3));
v___f_1947_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1939_);
v___f_1948_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1948_, 0, v_toFunctor_1939_);
v___f_1949_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1949_, 0, v_toFunctor_1939_);
v___x_1950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1950_, 0, v___f_1948_);
lean_ctor_set(v___x_1950_, 1, v___f_1949_);
v___f_1951_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1951_, 0, v_toSeqRight_1942_);
v___f_1952_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1952_, 0, v_toSeqLeft_1941_);
v___f_1953_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1953_, 0, v_toSeq_1940_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v___f_1951_);
lean_ctor_set(v___x_1944_, 3, v___f_1952_);
lean_ctor_set(v___x_1944_, 2, v___f_1953_);
lean_ctor_set(v___x_1944_, 1, v___f_1946_);
lean_ctor_set(v___x_1944_, 0, v___x_1950_);
v___x_1955_ = v___x_1944_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v___x_1950_);
lean_ctor_set(v_reuseFailAlloc_1967_, 1, v___f_1946_);
lean_ctor_set(v_reuseFailAlloc_1967_, 2, v___f_1953_);
lean_ctor_set(v_reuseFailAlloc_1967_, 3, v___f_1952_);
lean_ctor_set(v_reuseFailAlloc_1967_, 4, v___f_1951_);
v___x_1955_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
lean_object* v___x_1957_; 
if (v_isShared_1938_ == 0)
{
lean_ctor_set(v___x_1937_, 1, v___f_1947_);
lean_ctor_set(v___x_1937_, 0, v___x_1955_);
v___x_1957_ = v___x_1937_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1955_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v___f_1947_);
v___x_1957_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___f_1963_; lean_object* v___x_16782__overap_1964_; lean_object* v___x_1965_; 
v___x_1958_ = l_StateRefT_x27_instMonad___redArg(v___x_1957_);
v___x_1959_ = l_ReaderT_instMonad___redArg(v___x_1958_);
v___x_1960_ = l_StateRefT_x27_instMonad___redArg(v___x_1959_);
v___x_1961_ = lean_box(0);
v___x_1962_ = l_instInhabitedOfMonad___redArg(v___x_1960_, v___x_1961_);
v___f_1963_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1963_, 0, v___x_1962_);
v___x_16782__overap_1964_ = lean_panic_fn_borrowed(v___f_1963_, v_msg_1899_);
lean_dec_ref(v___f_1963_);
lean_inc(v___y_1907_);
lean_inc_ref(v___y_1906_);
lean_inc(v___y_1905_);
lean_inc_ref(v___y_1904_);
lean_inc(v___y_1903_);
lean_inc_ref(v___y_1902_);
lean_inc(v___y_1901_);
lean_inc_ref(v___y_1900_);
v___x_1965_ = lean_apply_9(v___x_16782__overap_1964_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_, v___y_1907_, lean_box(0));
return v___x_1965_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1___boxed(lean_object* v_msg_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1(v_msg_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
return v_res_1988_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1989_; double v___x_1990_; 
v___x_1989_ = lean_unsigned_to_nat(0u);
v___x_1990_ = lean_float_of_nat(v___x_1989_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg(lean_object* v_cls_1994_, lean_object* v_msg_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
lean_object* v_ref_2001_; lean_object* v___x_2002_; lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2047_; 
v_ref_2001_ = lean_ctor_get(v___y_1998_, 5);
v___x_2002_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_M_atomsAssignment_updateAtomsAssignment_spec__0_spec__0(v_msg_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2005_ = v___x_2002_;
v_isShared_2006_ = v_isSharedCheck_2047_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_2002_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2047_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2007_; lean_object* v_traceState_2008_; lean_object* v_env_2009_; lean_object* v_nextMacroScope_2010_; lean_object* v_ngen_2011_; lean_object* v_auxDeclNGen_2012_; lean_object* v_cache_2013_; lean_object* v_messages_2014_; lean_object* v_infoState_2015_; lean_object* v_snapshotTasks_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2046_; 
v___x_2007_ = lean_st_ref_take(v___y_1999_);
v_traceState_2008_ = lean_ctor_get(v___x_2007_, 4);
v_env_2009_ = lean_ctor_get(v___x_2007_, 0);
v_nextMacroScope_2010_ = lean_ctor_get(v___x_2007_, 1);
v_ngen_2011_ = lean_ctor_get(v___x_2007_, 2);
v_auxDeclNGen_2012_ = lean_ctor_get(v___x_2007_, 3);
v_cache_2013_ = lean_ctor_get(v___x_2007_, 5);
v_messages_2014_ = lean_ctor_get(v___x_2007_, 6);
v_infoState_2015_ = lean_ctor_get(v___x_2007_, 7);
v_snapshotTasks_2016_ = lean_ctor_get(v___x_2007_, 8);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2018_ = v___x_2007_;
v_isShared_2019_ = v_isSharedCheck_2046_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_snapshotTasks_2016_);
lean_inc(v_infoState_2015_);
lean_inc(v_messages_2014_);
lean_inc(v_cache_2013_);
lean_inc(v_traceState_2008_);
lean_inc(v_auxDeclNGen_2012_);
lean_inc(v_ngen_2011_);
lean_inc(v_nextMacroScope_2010_);
lean_inc(v_env_2009_);
lean_dec(v___x_2007_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2046_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
uint64_t v_tid_2020_; lean_object* v_traces_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2045_; 
v_tid_2020_ = lean_ctor_get_uint64(v_traceState_2008_, sizeof(void*)*1);
v_traces_2021_ = lean_ctor_get(v_traceState_2008_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v_traceState_2008_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2023_ = v_traceState_2008_;
v_isShared_2024_ = v_isSharedCheck_2045_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_traces_2021_);
lean_dec(v_traceState_2008_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2045_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2025_; double v___x_2026_; uint8_t v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2035_; 
v___x_2025_ = lean_box(0);
v___x_2026_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___closed__0);
v___x_2027_ = 0;
v___x_2028_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___closed__1));
v___x_2029_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2029_, 0, v_cls_1994_);
lean_ctor_set(v___x_2029_, 1, v___x_2025_);
lean_ctor_set(v___x_2029_, 2, v___x_2028_);
lean_ctor_set_float(v___x_2029_, sizeof(void*)*3, v___x_2026_);
lean_ctor_set_float(v___x_2029_, sizeof(void*)*3 + 8, v___x_2026_);
lean_ctor_set_uint8(v___x_2029_, sizeof(void*)*3 + 16, v___x_2027_);
v___x_2030_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___closed__2));
v___x_2031_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2029_);
lean_ctor_set(v___x_2031_, 1, v_a_2003_);
lean_ctor_set(v___x_2031_, 2, v___x_2030_);
lean_inc(v_ref_2001_);
v___x_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2032_, 0, v_ref_2001_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
v___x_2033_ = l_Lean_PersistentArray_push___redArg(v_traces_2021_, v___x_2032_);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 0, v___x_2033_);
v___x_2035_ = v___x_2023_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2033_);
lean_ctor_set_uint64(v_reuseFailAlloc_2044_, sizeof(void*)*1, v_tid_2020_);
v___x_2035_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
lean_object* v___x_2037_; 
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 4, v___x_2035_);
v___x_2037_ = v___x_2018_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_env_2009_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v_nextMacroScope_2010_);
lean_ctor_set(v_reuseFailAlloc_2043_, 2, v_ngen_2011_);
lean_ctor_set(v_reuseFailAlloc_2043_, 3, v_auxDeclNGen_2012_);
lean_ctor_set(v_reuseFailAlloc_2043_, 4, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2043_, 5, v_cache_2013_);
lean_ctor_set(v_reuseFailAlloc_2043_, 6, v_messages_2014_);
lean_ctor_set(v_reuseFailAlloc_2043_, 7, v_infoState_2015_);
lean_ctor_set(v_reuseFailAlloc_2043_, 8, v_snapshotTasks_2016_);
v___x_2037_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2041_; 
v___x_2038_ = lean_st_ref_put(v___y_1999_, v___x_2037_);
v___x_2039_ = lean_box(0);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 0, v___x_2039_);
v___x_2041_ = v___x_2005_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2039_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg___boxed(lean_object* v_cls_2048_, lean_object* v_msg_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg(v_cls_2048_, v_msg_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
return v_res_2055_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__0(void){
_start:
{
lean_object* v_cellCount_2056_; lean_object* v___x_2057_; 
v_cellCount_2056_ = lean_unsigned_to_nat(16u);
v___x_2057_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2056_);
return v___x_2057_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__1(void){
_start:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2058_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__0, &l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__0);
v___x_2059_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_M_run___redArg___closed__0);
v___x_2060_ = lean_unsigned_to_nat(0u);
v___x_2061_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2060_);
lean_ctor_set(v___x_2061_, 1, v___x_2059_);
lean_ctor_set(v___x_2061_, 2, v___x_2058_);
return v___x_2061_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__7(void){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2071_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__4));
v___x_2072_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__6));
v___x_2073_ = l_Lean_Name_append(v___x_2072_, v___x_2071_);
return v___x_2073_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__9(void){
_start:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2075_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__8));
v___x_2076_ = l_Lean_stringToMessageData(v___x_2075_);
return v___x_2076_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__11(void){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2078_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__10));
v___x_2079_ = l_Lean_stringToMessageData(v___x_2078_);
return v___x_2079_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__13(void){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2081_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__12));
v___x_2082_ = l_Lean_stringToMessageData(v___x_2081_);
return v___x_2082_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__17(void){
_start:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2086_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__16));
v___x_2087_ = lean_unsigned_to_nat(6u);
v___x_2088_ = lean_unsigned_to_nat(318u);
v___x_2089_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__15));
v___x_2090_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__14));
v___x_2091_ = l_mkPanicMessageWithDecl(v___x_2090_, v___x_2089_, v___x_2088_, v___x_2087_, v___x_2086_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_lookup(lean_object* v_e_2092_, lean_object* v_width_2093_, uint8_t v_synthetic_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_){
_start:
{
lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2107_; lean_object* v___y_2114_; lean_object* v___y_2115_; lean_object* v___y_2116_; lean_object* v___y_2117_; lean_object* v_i_2118_; lean_object* v___y_2124_; lean_object* v___y_2125_; lean_object* v___y_2126_; lean_object* v___y_2127_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v_i_2142_; lean_object* v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v___y_2161_; lean_object* v___x_2192_; lean_object* v_atoms_2193_; lean_object* v___x_2194_; 
v___x_2192_ = lean_st_ref_get(v_a_2096_);
v_atoms_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc_ref(v_atoms_2193_);
lean_dec(v___x_2192_);
v___x_2194_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_atoms_2193_, v_e_2092_);
lean_dec_ref(v_atoms_2193_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_options_2195_; uint8_t v_hasTrace_2196_; 
v_options_2195_ = lean_ctor_get(v_a_2101_, 2);
v_hasTrace_2196_ = lean_ctor_get_uint8(v_options_2195_, sizeof(void*)*1);
if (v_hasTrace_2196_ == 0)
{
v___y_2161_ = v_a_2096_;
goto v___jp_2160_;
}
else
{
lean_object* v_inheritedTraceOptions_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; uint8_t v___x_2200_; 
v_inheritedTraceOptions_2197_ = lean_ctor_get(v_a_2101_, 13);
v___x_2198_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__4));
v___x_2199_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__7, &l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__7);
v___x_2200_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2197_, v_options_2195_, v___x_2199_);
if (v___x_2200_ == 0)
{
v___y_2161_ = v_a_2096_;
goto v___jp_2160_;
}
else
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___y_2209_; 
v___x_2201_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__9, &l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__9);
lean_inc(v_width_2093_);
v___x_2202_ = l_Nat_reprFast(v_width_2093_);
v___x_2203_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
v___x_2204_ = l_Lean_MessageData_ofFormat(v___x_2203_);
v___x_2205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2201_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
v___x_2206_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__11, &l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__11);
v___x_2207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2205_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
if (v_synthetic_2094_ == 0)
{
lean_object* v___x_2226_; 
v___x_2226_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__7));
v___y_2209_ = v___x_2226_;
goto v___jp_2208_;
}
else
{
lean_object* v___x_2227_; 
v___x_2227_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__10));
v___y_2209_ = v___x_2227_;
goto v___jp_2208_;
}
v___jp_2208_:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
lean_inc_ref(v___y_2209_);
v___x_2210_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2210_, 0, v___y_2209_);
v___x_2211_ = l_Lean_MessageData_ofFormat(v___x_2210_);
v___x_2212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2207_);
lean_ctor_set(v___x_2212_, 1, v___x_2211_);
v___x_2213_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__13, &l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__13);
v___x_2214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2212_);
lean_ctor_set(v___x_2214_, 1, v___x_2213_);
lean_inc_ref(v_e_2092_);
v___x_2215_ = l_Lean_MessageData_ofExpr(v_e_2092_);
v___x_2216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2214_);
lean_ctor_set(v___x_2216_, 1, v___x_2215_);
v___x_2217_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg(v___x_2198_, v___x_2216_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_dec_ref_known(v___x_2217_, 1);
v___y_2161_ = v_a_2096_;
goto v___jp_2160_;
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec(v_width_2093_);
lean_dec_ref(v_e_2092_);
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2217_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2217_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2217_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2256_; 
lean_dec_ref(v_e_2092_);
v_val_2228_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2230_ = v___x_2194_;
v_isShared_2231_ = v_isSharedCheck_2256_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_val_2228_);
lean_dec(v___x_2194_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2256_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v_width_2232_; lean_object* v_atomNumber_2233_; uint8_t v___x_2234_; 
v_width_2232_ = lean_ctor_get(v_val_2228_, 0);
lean_inc(v_width_2232_);
v_atomNumber_2233_ = lean_ctor_get(v_val_2228_, 1);
lean_inc(v_atomNumber_2233_);
lean_dec(v_val_2228_);
v___x_2234_ = lean_nat_dec_eq(v_width_2093_, v_width_2232_);
lean_dec(v_width_2232_);
lean_dec(v_width_2093_);
if (v___x_2234_ == 0)
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
lean_del_object(v___x_2230_);
v___x_2235_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__17, &l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__17);
v___x_2236_ = l_panic___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__1(v___x_2235_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2243_; 
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2243_ == 0)
{
lean_object* v_unused_2244_; 
v_unused_2244_ = lean_ctor_get(v___x_2236_, 0);
lean_dec(v_unused_2244_);
v___x_2238_ = v___x_2236_;
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
else
{
lean_dec(v___x_2236_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2243_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2241_; 
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 0, v_atomNumber_2233_);
v___x_2241_ = v___x_2238_;
goto v_reusejp_2240_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_atomNumber_2233_);
v___x_2241_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2240_;
}
v_reusejp_2240_:
{
return v___x_2241_;
}
}
}
else
{
lean_object* v_a_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2252_; 
lean_dec(v_atomNumber_2233_);
v_a_2245_ = lean_ctor_get(v___x_2236_, 0);
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2252_ == 0)
{
v___x_2247_ = v___x_2236_;
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_a_2245_);
lean_dec(v___x_2236_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2252_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___x_2250_; 
if (v_isShared_2248_ == 0)
{
v___x_2250_ = v___x_2247_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_a_2245_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
}
else
{
lean_object* v___x_2254_; 
if (v_isShared_2231_ == 0)
{
lean_ctor_set_tag(v___x_2230_, 0);
lean_ctor_set(v___x_2230_, 0, v_atomNumber_2233_);
v___x_2254_ = v___x_2230_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_atomNumber_2233_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
v___jp_2104_:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2108_ = lean_box(0);
v___x_2109_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__1, &l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_M_lookup___closed__1);
v___x_2110_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2110_, 0, v___y_2107_);
lean_ctor_set(v___x_2110_, 1, v___x_2108_);
lean_ctor_set(v___x_2110_, 2, v___x_2109_);
v___x_2111_ = lean_st_ref_put(v___y_2106_, v___x_2110_);
v___x_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2112_, 0, v___y_2105_);
return v___x_2112_;
}
v___jp_2113_:
{
lean_object* v_size_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v_size_2119_ = lean_ctor_get(v___y_2115_, 0);
v___x_2120_ = lean_unsigned_to_nat(1u);
v___x_2121_ = lean_nat_add(v_size_2119_, v___x_2120_);
v___x_2122_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2115_, v___x_2121_, v_i_2118_, v_e_2092_, v___y_2116_);
lean_dec(v_i_2118_);
v___y_2105_ = v___y_2114_;
v___y_2106_ = v___y_2117_;
v___y_2107_ = v___x_2122_;
goto v___jp_2104_;
}
v___jp_2123_:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2128_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2___redArg(v___y_2125_);
lean_dec_ref(v___y_2125_);
v___x_2129_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v___x_2128_, v_e_2092_);
switch(lean_obj_tag(v___x_2129_))
{
case 0:
{
lean_object* v_index_2130_; lean_object* v_size_2131_; lean_object* v___x_2132_; 
v_index_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_index_2130_);
lean_dec_ref_known(v___x_2129_, 3);
v_size_2131_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_size_2131_);
v___x_2132_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2128_, v_size_2131_, v_index_2130_, v_e_2092_, v___y_2126_);
lean_dec(v_index_2130_);
v___y_2105_ = v___y_2124_;
v___y_2106_ = v___y_2127_;
v___y_2107_ = v___x_2132_;
goto v___jp_2104_;
}
case 1:
{
lean_object* v_index_2133_; 
v_index_2133_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_index_2133_);
lean_dec_ref_known(v___x_2129_, 1);
v___y_2114_ = v___y_2124_;
v___y_2115_ = v___x_2128_;
v___y_2116_ = v___y_2126_;
v___y_2117_ = v___y_2127_;
v_i_2118_ = v_index_2133_;
goto v___jp_2113_;
}
default: 
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2134_ = lean_unsigned_to_nat(0u);
v___x_2135_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2128_, v___x_2134_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_index_2136_; 
v_index_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_index_2136_);
lean_dec_ref_known(v___x_2135_, 1);
v___y_2114_ = v___y_2124_;
v___y_2115_ = v___x_2128_;
v___y_2116_ = v___y_2126_;
v___y_2117_ = v___y_2127_;
v_i_2118_ = v_index_2136_;
goto v___jp_2113_;
}
else
{
lean_dec_ref(v___y_2126_);
lean_dec_ref(v_e_2092_);
v___y_2105_ = v___y_2124_;
v___y_2106_ = v___y_2127_;
v___y_2107_ = v___x_2128_;
goto v___jp_2104_;
}
}
}
}
v___jp_2137_:
{
lean_object* v_size_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v_size_2143_ = lean_ctor_get(v___y_2141_, 0);
v___x_2144_ = lean_unsigned_to_nat(1u);
v___x_2145_ = lean_nat_add(v_size_2143_, v___x_2144_);
v___x_2146_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2141_, v___x_2145_, v_i_2142_, v_e_2092_, v___y_2139_);
lean_dec(v_i_2142_);
v___y_2105_ = v___y_2138_;
v___y_2106_ = v___y_2140_;
v___y_2107_ = v___x_2146_;
goto v___jp_2104_;
}
v___jp_2147_:
{
lean_object* v___x_2152_; 
v___x_2152_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v___y_2151_, v_e_2092_);
switch(lean_obj_tag(v___x_2152_))
{
case 0:
{
lean_object* v_index_2153_; lean_object* v_size_2154_; lean_object* v___x_2155_; 
v_index_2153_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_index_2153_);
lean_dec_ref_known(v___x_2152_, 3);
v_size_2154_ = lean_ctor_get(v___y_2151_, 0);
lean_inc(v_size_2154_);
v___x_2155_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2151_, v_size_2154_, v_index_2153_, v_e_2092_, v___y_2149_);
lean_dec(v_index_2153_);
v___y_2105_ = v___y_2148_;
v___y_2106_ = v___y_2150_;
v___y_2107_ = v___x_2155_;
goto v___jp_2104_;
}
case 1:
{
lean_object* v_index_2156_; 
v_index_2156_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_index_2156_);
lean_dec_ref_known(v___x_2152_, 1);
v___y_2138_ = v___y_2148_;
v___y_2139_ = v___y_2149_;
v___y_2140_ = v___y_2150_;
v___y_2141_ = v___y_2151_;
v_i_2142_ = v_index_2156_;
goto v___jp_2137_;
}
default: 
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = lean_unsigned_to_nat(0u);
v___x_2158_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2151_, v___x_2157_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_index_2159_; 
v_index_2159_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_index_2159_);
lean_dec_ref_known(v___x_2158_, 1);
v___y_2138_ = v___y_2148_;
v___y_2139_ = v___y_2149_;
v___y_2140_ = v___y_2150_;
v___y_2141_ = v___y_2151_;
v_i_2142_ = v_index_2159_;
goto v___jp_2137_;
}
else
{
lean_dec_ref(v___y_2149_);
lean_dec_ref(v_e_2092_);
v___y_2105_ = v___y_2148_;
v___y_2106_ = v___y_2150_;
v___y_2107_ = v___y_2151_;
goto v___jp_2104_;
}
}
}
}
v___jp_2160_:
{
lean_object* v___x_2162_; lean_object* v_atoms_2163_; lean_object* v_size_2164_; lean_object* v_keyArray_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2162_ = lean_st_ref_take(v___y_2161_);
v_atoms_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc_ref(v_atoms_2163_);
lean_dec(v___x_2162_);
v_size_2164_ = lean_ctor_get(v_atoms_2163_, 0);
lean_inc_n(v_size_2164_, 2);
v_keyArray_2165_ = lean_ctor_get(v_atoms_2163_, 1);
v___x_2166_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2166_, 0, v_width_2093_);
lean_ctor_set(v___x_2166_, 1, v_size_2164_);
lean_ctor_set_uint8(v___x_2166_, sizeof(void*)*2, v_synthetic_2094_);
v___x_2167_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v_atoms_2163_, v_e_2092_);
switch(lean_obj_tag(v___x_2167_))
{
case 0:
{
lean_object* v_index_2168_; lean_object* v___x_2169_; 
v_index_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_index_2168_);
lean_dec_ref_known(v___x_2167_, 3);
lean_inc(v_size_2164_);
v___x_2169_ = l_Std_DHashMap_Raw_setEntry___redArg(v_atoms_2163_, v_size_2164_, v_index_2168_, v_e_2092_, v___x_2166_);
lean_dec(v_index_2168_);
v___y_2105_ = v_size_2164_;
v___y_2106_ = v___y_2161_;
v___y_2107_ = v___x_2169_;
goto v___jp_2104_;
}
case 1:
{
lean_object* v_index_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; uint8_t v___x_2174_; 
v_index_2170_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_index_2170_);
lean_dec_ref_known(v___x_2167_, 1);
v___x_2171_ = lean_unsigned_to_nat(1u);
v___x_2172_ = lean_nat_add(v_size_2164_, v___x_2171_);
v___x_2173_ = lean_array_get_size(v_keyArray_2165_);
v___x_2174_ = lean_nat_dec_lt(v___x_2172_, v___x_2173_);
if (v___x_2174_ == 0)
{
lean_dec(v___x_2172_);
lean_dec(v_index_2170_);
v___y_2124_ = v_size_2164_;
v___y_2125_ = v_atoms_2163_;
v___y_2126_ = v___x_2166_;
v___y_2127_ = v___y_2161_;
goto v___jp_2123_;
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; uint8_t v___x_2179_; 
v___x_2175_ = lean_unsigned_to_nat(4u);
v___x_2176_ = lean_nat_mul(v___x_2172_, v___x_2175_);
v___x_2177_ = lean_unsigned_to_nat(3u);
v___x_2178_ = lean_nat_mul(v___x_2173_, v___x_2177_);
v___x_2179_ = lean_nat_dec_le(v___x_2176_, v___x_2178_);
lean_dec(v___x_2178_);
lean_dec(v___x_2176_);
if (v___x_2179_ == 0)
{
lean_dec(v___x_2172_);
lean_dec(v_index_2170_);
v___y_2124_ = v_size_2164_;
v___y_2125_ = v_atoms_2163_;
v___y_2126_ = v___x_2166_;
v___y_2127_ = v___y_2161_;
goto v___jp_2123_;
}
else
{
lean_object* v___x_2180_; 
v___x_2180_ = l_Std_DHashMap_Raw_setEntry___redArg(v_atoms_2163_, v___x_2172_, v_index_2170_, v_e_2092_, v___x_2166_);
lean_dec(v_index_2170_);
v___y_2105_ = v_size_2164_;
v___y_2106_ = v___y_2161_;
v___y_2107_ = v___x_2180_;
goto v___jp_2104_;
}
}
}
default: 
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; uint8_t v___x_2184_; 
v___x_2181_ = lean_unsigned_to_nat(1u);
v___x_2182_ = lean_nat_add(v_size_2164_, v___x_2181_);
v___x_2183_ = lean_array_get_size(v_keyArray_2165_);
v___x_2184_ = lean_nat_dec_lt(v___x_2182_, v___x_2183_);
if (v___x_2184_ == 0)
{
lean_object* v___x_2185_; 
lean_dec(v___x_2182_);
v___x_2185_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2___redArg(v_atoms_2163_);
lean_dec_ref(v_atoms_2163_);
v___y_2148_ = v_size_2164_;
v___y_2149_ = v___x_2166_;
v___y_2150_ = v___y_2161_;
v___y_2151_ = v___x_2185_;
goto v___jp_2147_;
}
else
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; uint8_t v___x_2190_; 
v___x_2186_ = lean_unsigned_to_nat(4u);
v___x_2187_ = lean_nat_mul(v___x_2182_, v___x_2186_);
lean_dec(v___x_2182_);
v___x_2188_ = lean_unsigned_to_nat(3u);
v___x_2189_ = lean_nat_mul(v___x_2183_, v___x_2188_);
v___x_2190_ = lean_nat_dec_le(v___x_2187_, v___x_2189_);
lean_dec(v___x_2189_);
lean_dec(v___x_2187_);
if (v___x_2190_ == 0)
{
lean_object* v___x_2191_; 
v___x_2191_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__2___redArg(v_atoms_2163_);
lean_dec_ref(v_atoms_2163_);
v___y_2148_ = v_size_2164_;
v___y_2149_ = v___x_2166_;
v___y_2150_ = v___y_2161_;
v___y_2151_ = v___x_2191_;
goto v___jp_2147_;
}
else
{
v___y_2148_ = v_size_2164_;
v___y_2149_ = v___x_2166_;
v___y_2150_ = v___y_2161_;
v___y_2151_ = v_atoms_2163_;
goto v___jp_2147_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_lookup___boxed(lean_object* v_e_2257_, lean_object* v_width_2258_, lean_object* v_synthetic_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_){
_start:
{
uint8_t v_synthetic_boxed_2269_; lean_object* v_res_2270_; 
v_synthetic_boxed_2269_ = lean_unbox(v_synthetic_2259_);
v_res_2270_ = l_Lean_Meta_Tactic_BVDecide_M_lookup(v_e_2257_, v_width_2258_, v_synthetic_boxed_2269_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_);
lean_dec(v_a_2267_);
lean_dec_ref(v_a_2266_);
lean_dec(v_a_2265_);
lean_dec_ref(v_a_2264_);
lean_dec(v_a_2263_);
lean_dec_ref(v_a_2262_);
lean_dec(v_a_2261_);
lean_dec_ref(v_a_2260_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0(lean_object* v_cls_2271_, lean_object* v_msg_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
lean_object* v___x_2282_; 
v___x_2282_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___redArg(v_cls_2271_, v_msg_2272_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0___boxed(lean_object* v_cls_2283_, lean_object* v_msg_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_M_lookup_spec__0(v_cls_2283_, v_msg_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27(lean_object* v_mkFRefl_2295_, lean_object* v_fst_2296_, lean_object* v_fproof_2297_, lean_object* v_mkSRefl_2298_, lean_object* v_snd_2299_, lean_object* v_sproof_2300_){
_start:
{
if (lean_obj_tag(v_fproof_2297_) == 0)
{
lean_dec_ref(v_snd_2299_);
lean_dec_ref(v_mkSRefl_2298_);
if (lean_obj_tag(v_sproof_2300_) == 0)
{
lean_object* v___x_2301_; 
lean_dec_ref(v_fst_2296_);
lean_dec_ref(v_mkFRefl_2295_);
v___x_2301_ = lean_box(0);
return v___x_2301_;
}
else
{
lean_object* v_val_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2311_; 
v_val_2302_ = lean_ctor_get(v_sproof_2300_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v_sproof_2300_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2304_ = v_sproof_2300_;
v_isShared_2305_ = v_isSharedCheck_2311_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_val_2302_);
lean_dec(v_sproof_2300_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2311_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2309_; 
v___x_2306_ = lean_apply_1(v_mkFRefl_2295_, v_fst_2296_);
v___x_2307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
lean_ctor_set(v___x_2307_, 1, v_val_2302_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 0, v___x_2307_);
v___x_2309_ = v___x_2304_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v___x_2307_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
else
{
lean_dec_ref(v_fst_2296_);
lean_dec_ref(v_mkFRefl_2295_);
if (lean_obj_tag(v_sproof_2300_) == 0)
{
lean_object* v_val_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2321_; 
v_val_2312_ = lean_ctor_get(v_fproof_2297_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v_fproof_2297_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2314_ = v_fproof_2297_;
v_isShared_2315_ = v_isSharedCheck_2321_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_val_2312_);
lean_dec(v_fproof_2297_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2321_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2319_; 
v___x_2316_ = lean_apply_1(v_mkSRefl_2298_, v_snd_2299_);
v___x_2317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2317_, 0, v_val_2312_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 0, v___x_2317_);
v___x_2319_ = v___x_2314_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2317_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
else
{
lean_object* v_val_2322_; lean_object* v_val_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2331_; 
lean_dec_ref(v_snd_2299_);
lean_dec_ref(v_mkSRefl_2298_);
v_val_2322_ = lean_ctor_get(v_fproof_2297_, 0);
lean_inc(v_val_2322_);
lean_dec_ref_known(v_fproof_2297_, 1);
v_val_2323_ = lean_ctor_get(v_sproof_2300_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v_sproof_2300_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2325_ = v_sproof_2300_;
v_isShared_2326_ = v_isSharedCheck_2331_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_val_2323_);
lean_dec(v_sproof_2300_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2331_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2327_; lean_object* v___x_2329_; 
v___x_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2327_, 0, v_val_2322_);
lean_ctor_set(v___x_2327_, 1, v_val_2323_);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 0, v___x_2327_);
v___x_2329_ = v___x_2325_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2327_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof(lean_object* v_mkRefl_2332_, lean_object* v_fst_2333_, lean_object* v_fproof_2334_, lean_object* v_snd_2335_, lean_object* v_sproof_2336_){
_start:
{
lean_object* v___x_2337_; 
lean_inc_ref(v_mkRefl_2332_);
v___x_2337_ = l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27(v_mkRefl_2332_, v_fst_2333_, v_fproof_2334_, v_mkRefl_2332_, v_snd_2335_, v_sproof_2336_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_simplifyTernaryProof(lean_object* v_mkRefl_2338_, lean_object* v_fst_2339_, lean_object* v_fproof_2340_, lean_object* v_snd_2341_, lean_object* v_sproof_2342_, lean_object* v_thd_2343_, lean_object* v_tproof_2344_){
_start:
{
if (lean_obj_tag(v_fproof_2340_) == 0)
{
lean_object* v___x_2345_; 
lean_inc_ref_n(v_mkRefl_2338_, 2);
v___x_2345_ = l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27(v_mkRefl_2338_, v_snd_2341_, v_sproof_2342_, v_mkRefl_2338_, v_thd_2343_, v_tproof_2344_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v___x_2346_; 
lean_dec_ref(v_fst_2339_);
lean_dec_ref(v_mkRefl_2338_);
v___x_2346_ = lean_box(0);
return v___x_2346_;
}
else
{
lean_object* v_val_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2356_; 
v_val_2347_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2349_ = v___x_2345_;
v_isShared_2350_ = v_isSharedCheck_2356_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_val_2347_);
lean_dec(v___x_2345_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2356_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2354_; 
v___x_2351_ = lean_apply_1(v_mkRefl_2338_, v_fst_2339_);
v___x_2352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2351_);
lean_ctor_set(v___x_2352_, 1, v_val_2347_);
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 0, v___x_2352_);
v___x_2354_ = v___x_2349_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v___x_2352_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
else
{
lean_object* v_val_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2378_; 
lean_dec_ref(v_fst_2339_);
v_val_2357_ = lean_ctor_get(v_fproof_2340_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v_fproof_2340_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2359_ = v_fproof_2340_;
v_isShared_2360_ = v_isSharedCheck_2378_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_val_2357_);
lean_dec(v_fproof_2340_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2378_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2361_; 
lean_inc_ref(v_thd_2343_);
lean_inc_ref(v_snd_2341_);
lean_inc_ref_n(v_mkRefl_2338_, 2);
v___x_2361_ = l_Lean_Meta_Tactic_BVDecide_M_simplifyBinaryProof_x27(v_mkRefl_2338_, v_snd_2341_, v_sproof_2342_, v_mkRefl_2338_, v_thd_2343_, v_tproof_2344_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2367_; 
lean_inc_ref(v_mkRefl_2338_);
v___x_2362_ = lean_apply_1(v_mkRefl_2338_, v_snd_2341_);
v___x_2363_ = lean_apply_1(v_mkRefl_2338_, v_thd_2343_);
v___x_2364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2362_);
lean_ctor_set(v___x_2364_, 1, v___x_2363_);
v___x_2365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2365_, 0, v_val_2357_);
lean_ctor_set(v___x_2365_, 1, v___x_2364_);
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 0, v___x_2365_);
v___x_2367_ = v___x_2359_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2365_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
else
{
lean_object* v_val_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2377_; 
lean_del_object(v___x_2359_);
lean_dec_ref(v_thd_2343_);
lean_dec_ref(v_snd_2341_);
lean_dec_ref(v_mkRefl_2338_);
v_val_2369_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2371_ = v___x_2361_;
v_isShared_2372_ = v_isSharedCheck_2377_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_val_2369_);
lean_dec(v___x_2361_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2377_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2373_; lean_object* v___x_2375_; 
v___x_2373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2373_, 0, v_val_2357_);
lean_ctor_set(v___x_2373_, 1, v_val_2369_);
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 0, v___x_2373_);
v___x_2375_ = v___x_2371_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2373_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_getHyps___redArg(lean_object* v_a_2379_){
_start:
{
lean_object* v___x_2381_; 
lean_inc_ref(v_a_2379_);
v___x_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2381_, 0, v_a_2379_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_getHyps___redArg___boxed(lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Lean_Meta_Tactic_BVDecide_M_getHyps___redArg(v_a_2382_);
lean_dec_ref(v_a_2382_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_getHyps(lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_){
_start:
{
lean_object* v___x_2394_; 
lean_inc_ref(v_a_2385_);
v___x_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2394_, 0, v_a_2385_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_M_getHyps___boxed(lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Lean_Meta_Tactic_BVDecide_M_getHyps(v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
lean_dec(v_a_2400_);
lean_dec_ref(v_a_2399_);
lean_dec(v_a_2398_);
lean_dec_ref(v_a_2397_);
lean_dec(v_a_2396_);
lean_dec_ref(v_a_2395_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg(lean_object* v_m_2405_, lean_object* v_state_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_){
_start:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2416_ = lean_st_mk_ref(v_state_2406_);
lean_inc(v_a_2414_);
lean_inc_ref(v_a_2413_);
lean_inc(v_a_2412_);
lean_inc_ref(v_a_2411_);
lean_inc(v_a_2410_);
lean_inc_ref(v_a_2409_);
lean_inc(v_a_2408_);
lean_inc_ref(v_a_2407_);
lean_inc(v___x_2416_);
v___x_2417_ = lean_apply_10(v_m_2405_, v___x_2416_, v_a_2407_, v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_, v_a_2414_, lean_box(0));
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2428_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2420_ = v___x_2417_;
v_isShared_2421_ = v_isSharedCheck_2428_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_dec(v___x_2417_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2428_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2422_; lean_object* v_lemmas_2423_; lean_object* v___x_2424_; lean_object* v___x_2426_; 
v___x_2422_ = lean_st_ref_get(v___x_2416_);
lean_dec(v___x_2416_);
v_lemmas_2423_ = lean_ctor_get(v___x_2422_, 0);
lean_inc_ref(v_lemmas_2423_);
lean_dec(v___x_2422_);
v___x_2424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2424_, 0, v_a_2418_);
lean_ctor_set(v___x_2424_, 1, v_lemmas_2423_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 0, v___x_2424_);
v___x_2426_ = v___x_2420_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2424_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
else
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
lean_dec(v___x_2416_);
v_a_2429_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___x_2417_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2417_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2429_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg___boxed(lean_object* v_m_2437_, lean_object* v_state_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg(v_m_2437_, v_state_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_);
lean_dec(v_a_2446_);
lean_dec_ref(v_a_2445_);
lean_dec(v_a_2444_);
lean_dec_ref(v_a_2443_);
lean_dec(v_a_2442_);
lean_dec_ref(v_a_2441_);
lean_dec(v_a_2440_);
lean_dec_ref(v_a_2439_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_run(lean_object* v_00_u03b1_2449_, lean_object* v_m_2450_, lean_object* v_state_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_){
_start:
{
lean_object* v___x_2461_; 
v___x_2461_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg(v_m_2450_, v_state_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_run___boxed(lean_object* v_00_u03b1_2462_, lean_object* v_m_2463_, lean_object* v_state_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_run(v_00_u03b1_2462_, v_m_2463_, v_state_2464_, v_a_2465_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_, v_a_2472_);
lean_dec(v_a_2472_);
lean_dec_ref(v_a_2471_);
lean_dec(v_a_2470_);
lean_dec_ref(v_a_2469_);
lean_dec(v_a_2468_);
lean_dec_ref(v_a_2467_);
lean_dec(v_a_2466_);
lean_dec_ref(v_a_2465_);
return v_res_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg(lean_object* v_lemma_2475_, lean_object* v_a_2476_){
_start:
{
lean_object* v___x_2478_; lean_object* v_lemmas_2479_; lean_object* v_bvExprCache_2480_; lean_object* v_bvPredCache_2481_; lean_object* v_bvLogicalCache_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2493_; 
v___x_2478_ = lean_st_ref_take(v_a_2476_);
v_lemmas_2479_ = lean_ctor_get(v___x_2478_, 0);
v_bvExprCache_2480_ = lean_ctor_get(v___x_2478_, 1);
v_bvPredCache_2481_ = lean_ctor_get(v___x_2478_, 2);
v_bvLogicalCache_2482_ = lean_ctor_get(v___x_2478_, 3);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2484_ = v___x_2478_;
v_isShared_2485_ = v_isSharedCheck_2493_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_bvLogicalCache_2482_);
lean_inc(v_bvPredCache_2481_);
lean_inc(v_bvExprCache_2480_);
lean_inc(v_lemmas_2479_);
lean_dec(v___x_2478_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2493_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2486_; lean_object* v___x_2488_; 
v___x_2486_ = lean_array_push(v_lemmas_2479_, v_lemma_2475_);
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 0, v___x_2486_);
v___x_2488_ = v___x_2484_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2486_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v_bvExprCache_2480_);
lean_ctor_set(v_reuseFailAlloc_2492_, 2, v_bvPredCache_2481_);
lean_ctor_set(v_reuseFailAlloc_2492_, 3, v_bvLogicalCache_2482_);
v___x_2488_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2489_ = lean_st_ref_put(v_a_2476_, v___x_2488_);
v___x_2490_ = lean_box(0);
v___x_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2490_);
return v___x_2491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg___boxed(lean_object* v_lemma_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg(v_lemma_2494_, v_a_2495_);
lean_dec(v_a_2495_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma(lean_object* v_lemma_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_){
_start:
{
lean_object* v___x_2509_; 
v___x_2509_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg(v_lemma_2498_, v_a_2499_);
return v___x_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___boxed(lean_object* v_lemma_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma(v_lemma_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_);
lean_dec(v_a_2519_);
lean_dec_ref(v_a_2518_);
lean_dec(v_a_2517_);
lean_dec_ref(v_a_2516_);
lean_dec(v_a_2515_);
lean_dec_ref(v_a_2514_);
lean_dec(v_a_2513_);
lean_dec_ref(v_a_2512_);
lean_dec(v_a_2511_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache(lean_object* v_e_2524_, lean_object* v_f_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_){
_start:
{
lean_object* v___x_2536_; lean_object* v_bvExprCache_2537_; lean_object* v___f_2538_; lean_object* v___f_2539_; lean_object* v___x_2540_; 
v___x_2536_ = lean_st_ref_get(v_a_2526_);
v_bvExprCache_2537_ = lean_ctor_get(v___x_2536_, 1);
lean_inc_ref(v_bvExprCache_2537_);
lean_dec(v___x_2536_);
v___f_2538_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__0));
v___f_2539_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__1));
lean_inc_ref(v_e_2524_);
v___x_2540_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_2538_, v___f_2539_, v_bvExprCache_2537_, v_e_2524_);
lean_dec_ref(v_bvExprCache_2537_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v___x_2541_; 
lean_inc(v_a_2534_);
lean_inc_ref(v_a_2533_);
lean_inc(v_a_2532_);
lean_inc_ref(v_a_2531_);
lean_inc(v_a_2530_);
lean_inc_ref(v_a_2529_);
lean_inc(v_a_2528_);
lean_inc_ref(v_a_2527_);
lean_inc(v_a_2526_);
lean_inc_ref(v_e_2524_);
v___x_2541_ = lean_apply_11(v_f_2525_, v_e_2524_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, lean_box(0));
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2628_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2544_ = v___x_2541_;
v_isShared_2545_ = v_isSharedCheck_2628_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2541_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2628_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2546_; lean_object* v_lemmas_2547_; lean_object* v_bvExprCache_2548_; lean_object* v_bvPredCache_2549_; lean_object* v_bvLogicalCache_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2627_; 
v___x_2546_ = lean_st_ref_take(v_a_2526_);
v_lemmas_2547_ = lean_ctor_get(v___x_2546_, 0);
v_bvExprCache_2548_ = lean_ctor_get(v___x_2546_, 1);
v_bvPredCache_2549_ = lean_ctor_get(v___x_2546_, 2);
v_bvLogicalCache_2550_ = lean_ctor_get(v___x_2546_, 3);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2552_ = v___x_2546_;
v_isShared_2553_ = v_isSharedCheck_2627_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_bvLogicalCache_2550_);
lean_inc(v_bvPredCache_2549_);
lean_inc(v_bvExprCache_2548_);
lean_inc(v_lemmas_2547_);
lean_dec(v___x_2546_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2627_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___y_2555_; lean_object* v___y_2564_; lean_object* v_i_2565_; lean_object* v___y_2581_; lean_object* v_i_2582_; lean_object* v___y_2588_; lean_object* v___x_2597_; 
lean_inc_ref(v_e_2524_);
v___x_2597_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_2538_, v___f_2539_, v_bvExprCache_2548_, v_e_2524_);
switch(lean_obj_tag(v___x_2597_))
{
case 0:
{
lean_object* v_index_2598_; lean_object* v_size_2599_; lean_object* v___x_2600_; 
v_index_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_index_2598_);
lean_dec_ref_known(v___x_2597_, 3);
v_size_2599_ = lean_ctor_get(v_bvExprCache_2548_, 0);
lean_inc(v_size_2599_);
lean_inc(v_a_2542_);
v___x_2600_ = l_Std_DHashMap_Raw_setEntry___redArg(v_bvExprCache_2548_, v_size_2599_, v_index_2598_, v_e_2524_, v_a_2542_);
lean_dec(v_index_2598_);
v___y_2555_ = v___x_2600_;
goto v___jp_2554_;
}
case 1:
{
lean_object* v_index_2601_; lean_object* v_size_2602_; lean_object* v_keyArray_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; uint8_t v___x_2607_; 
v_index_2601_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_index_2601_);
lean_dec_ref_known(v___x_2597_, 1);
v_size_2602_ = lean_ctor_get(v_bvExprCache_2548_, 0);
v_keyArray_2603_ = lean_ctor_get(v_bvExprCache_2548_, 1);
v___x_2604_ = lean_unsigned_to_nat(1u);
v___x_2605_ = lean_nat_add(v_size_2602_, v___x_2604_);
v___x_2606_ = lean_array_get_size(v_keyArray_2603_);
v___x_2607_ = lean_nat_dec_lt(v___x_2605_, v___x_2606_);
if (v___x_2607_ == 0)
{
lean_dec(v___x_2605_);
lean_dec(v_index_2601_);
goto v___jp_2570_;
}
else
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; uint8_t v___x_2612_; 
v___x_2608_ = lean_unsigned_to_nat(4u);
v___x_2609_ = lean_nat_mul(v___x_2605_, v___x_2608_);
v___x_2610_ = lean_unsigned_to_nat(3u);
v___x_2611_ = lean_nat_mul(v___x_2606_, v___x_2610_);
v___x_2612_ = lean_nat_dec_le(v___x_2609_, v___x_2611_);
lean_dec(v___x_2611_);
lean_dec(v___x_2609_);
if (v___x_2612_ == 0)
{
lean_dec(v___x_2605_);
lean_dec(v_index_2601_);
goto v___jp_2570_;
}
else
{
lean_object* v___x_2613_; 
lean_inc(v_a_2542_);
v___x_2613_ = l_Std_DHashMap_Raw_setEntry___redArg(v_bvExprCache_2548_, v___x_2605_, v_index_2601_, v_e_2524_, v_a_2542_);
lean_dec(v_index_2601_);
v___y_2555_ = v___x_2613_;
goto v___jp_2554_;
}
}
}
default: 
{
lean_object* v_size_2614_; lean_object* v_keyArray_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; uint8_t v___x_2619_; 
v_size_2614_ = lean_ctor_get(v_bvExprCache_2548_, 0);
v_keyArray_2615_ = lean_ctor_get(v_bvExprCache_2548_, 1);
v___x_2616_ = lean_unsigned_to_nat(1u);
v___x_2617_ = lean_nat_add(v_size_2614_, v___x_2616_);
v___x_2618_ = lean_array_get_size(v_keyArray_2615_);
v___x_2619_ = lean_nat_dec_lt(v___x_2617_, v___x_2618_);
if (v___x_2619_ == 0)
{
lean_object* v___x_2620_; 
lean_dec(v___x_2617_);
v___x_2620_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_2538_, v___f_2539_, v_bvExprCache_2548_);
v___y_2588_ = v___x_2620_;
goto v___jp_2587_;
}
else
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; uint8_t v___x_2625_; 
v___x_2621_ = lean_unsigned_to_nat(4u);
v___x_2622_ = lean_nat_mul(v___x_2617_, v___x_2621_);
lean_dec(v___x_2617_);
v___x_2623_ = lean_unsigned_to_nat(3u);
v___x_2624_ = lean_nat_mul(v___x_2618_, v___x_2623_);
v___x_2625_ = lean_nat_dec_le(v___x_2622_, v___x_2624_);
lean_dec(v___x_2624_);
lean_dec(v___x_2622_);
if (v___x_2625_ == 0)
{
lean_object* v___x_2626_; 
v___x_2626_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_2538_, v___f_2539_, v_bvExprCache_2548_);
v___y_2588_ = v___x_2626_;
goto v___jp_2587_;
}
else
{
v___y_2588_ = v_bvExprCache_2548_;
goto v___jp_2587_;
}
}
}
}
v___jp_2554_:
{
lean_object* v___x_2557_; 
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 1, v___y_2555_);
v___x_2557_ = v___x_2552_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_lemmas_2547_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v___y_2555_);
lean_ctor_set(v_reuseFailAlloc_2562_, 2, v_bvPredCache_2549_);
lean_ctor_set(v_reuseFailAlloc_2562_, 3, v_bvLogicalCache_2550_);
v___x_2557_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
lean_object* v___x_2558_; lean_object* v___x_2560_; 
v___x_2558_ = lean_st_ref_put(v_a_2526_, v___x_2557_);
if (v_isShared_2545_ == 0)
{
v___x_2560_ = v___x_2544_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2542_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
v___jp_2563_:
{
lean_object* v_size_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v_size_2566_ = lean_ctor_get(v___y_2564_, 0);
v___x_2567_ = lean_unsigned_to_nat(1u);
v___x_2568_ = lean_nat_add(v_size_2566_, v___x_2567_);
lean_inc(v_a_2542_);
v___x_2569_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2564_, v___x_2568_, v_i_2565_, v_e_2524_, v_a_2542_);
lean_dec(v_i_2565_);
v___y_2555_ = v___x_2569_;
goto v___jp_2554_;
}
v___jp_2570_:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2571_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_2538_, v___f_2539_, v_bvExprCache_2548_);
lean_inc_ref(v_e_2524_);
v___x_2572_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_2538_, v___f_2539_, v___x_2571_, v_e_2524_);
switch(lean_obj_tag(v___x_2572_))
{
case 0:
{
lean_object* v_index_2573_; lean_object* v_size_2574_; lean_object* v___x_2575_; 
v_index_2573_ = lean_ctor_get(v___x_2572_, 0);
lean_inc(v_index_2573_);
lean_dec_ref_known(v___x_2572_, 3);
v_size_2574_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_size_2574_);
lean_inc(v_a_2542_);
v___x_2575_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2571_, v_size_2574_, v_index_2573_, v_e_2524_, v_a_2542_);
lean_dec(v_index_2573_);
v___y_2555_ = v___x_2575_;
goto v___jp_2554_;
}
case 1:
{
lean_object* v_index_2576_; 
v_index_2576_ = lean_ctor_get(v___x_2572_, 0);
lean_inc(v_index_2576_);
lean_dec_ref_known(v___x_2572_, 1);
v___y_2564_ = v___x_2571_;
v_i_2565_ = v_index_2576_;
goto v___jp_2563_;
}
default: 
{
lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2577_ = lean_unsigned_to_nat(0u);
v___x_2578_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2571_, v___x_2577_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v_index_2579_; 
v_index_2579_ = lean_ctor_get(v___x_2578_, 0);
lean_inc(v_index_2579_);
lean_dec_ref_known(v___x_2578_, 1);
v___y_2564_ = v___x_2571_;
v_i_2565_ = v_index_2579_;
goto v___jp_2563_;
}
else
{
lean_dec_ref(v_e_2524_);
v___y_2555_ = v___x_2571_;
goto v___jp_2554_;
}
}
}
}
v___jp_2580_:
{
lean_object* v_size_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v_size_2583_ = lean_ctor_get(v___y_2581_, 0);
v___x_2584_ = lean_unsigned_to_nat(1u);
v___x_2585_ = lean_nat_add(v_size_2583_, v___x_2584_);
lean_inc(v_a_2542_);
v___x_2586_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2581_, v___x_2585_, v_i_2582_, v_e_2524_, v_a_2542_);
lean_dec(v_i_2582_);
v___y_2555_ = v___x_2586_;
goto v___jp_2554_;
}
v___jp_2587_:
{
lean_object* v___x_2589_; 
lean_inc_ref(v_e_2524_);
v___x_2589_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_2538_, v___f_2539_, v___y_2588_, v_e_2524_);
switch(lean_obj_tag(v___x_2589_))
{
case 0:
{
lean_object* v_index_2590_; lean_object* v_size_2591_; lean_object* v___x_2592_; 
v_index_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_index_2590_);
lean_dec_ref_known(v___x_2589_, 3);
v_size_2591_ = lean_ctor_get(v___y_2588_, 0);
lean_inc(v_size_2591_);
lean_inc(v_a_2542_);
v___x_2592_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2588_, v_size_2591_, v_index_2590_, v_e_2524_, v_a_2542_);
lean_dec(v_index_2590_);
v___y_2555_ = v___x_2592_;
goto v___jp_2554_;
}
case 1:
{
lean_object* v_index_2593_; 
v_index_2593_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_index_2593_);
lean_dec_ref_known(v___x_2589_, 1);
v___y_2581_ = v___y_2588_;
v_i_2582_ = v_index_2593_;
goto v___jp_2580_;
}
default: 
{
lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2594_ = lean_unsigned_to_nat(0u);
v___x_2595_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2588_, v___x_2594_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_index_2596_; 
v_index_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_index_2596_);
lean_dec_ref_known(v___x_2595_, 1);
v___y_2581_ = v___y_2588_;
v_i_2582_ = v_index_2596_;
goto v___jp_2580_;
}
else
{
lean_dec_ref(v_e_2524_);
v___y_2555_ = v___y_2588_;
goto v___jp_2554_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2524_);
return v___x_2541_;
}
}
else
{
lean_object* v_val_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
lean_dec_ref(v_f_2525_);
lean_dec_ref(v_e_2524_);
v_val_2629_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2540_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_val_2629_);
lean_dec(v___x_2540_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
lean_ctor_set_tag(v___x_2631_, 0);
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_val_2629_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___boxed(lean_object* v_e_2637_, lean_object* v_f_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache(v_e_2637_, v_f_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_);
lean_dec(v_a_2647_);
lean_dec_ref(v_a_2646_);
lean_dec(v_a_2645_);
lean_dec_ref(v_a_2644_);
lean_dec(v_a_2643_);
lean_dec_ref(v_a_2642_);
lean_dec(v_a_2641_);
lean_dec_ref(v_a_2640_);
lean_dec(v_a_2639_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache(lean_object* v_e_2650_, lean_object* v_f_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_){
_start:
{
lean_object* v___x_2662_; lean_object* v_bvPredCache_2663_; lean_object* v___f_2664_; lean_object* v___f_2665_; lean_object* v___x_2666_; 
v___x_2662_ = lean_st_ref_get(v_a_2652_);
v_bvPredCache_2663_ = lean_ctor_get(v___x_2662_, 2);
lean_inc_ref(v_bvPredCache_2663_);
lean_dec(v___x_2662_);
v___f_2664_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__0));
v___f_2665_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__1));
lean_inc_ref(v_e_2650_);
v___x_2666_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_2664_, v___f_2665_, v_bvPredCache_2663_, v_e_2650_);
lean_dec_ref(v_bvPredCache_2663_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v___x_2667_; 
lean_inc(v_a_2660_);
lean_inc_ref(v_a_2659_);
lean_inc(v_a_2658_);
lean_inc_ref(v_a_2657_);
lean_inc(v_a_2656_);
lean_inc_ref(v_a_2655_);
lean_inc(v_a_2654_);
lean_inc_ref(v_a_2653_);
lean_inc(v_a_2652_);
lean_inc_ref(v_e_2650_);
v___x_2667_ = lean_apply_11(v_f_2651_, v_e_2650_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, lean_box(0));
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2754_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2670_ = v___x_2667_;
v_isShared_2671_ = v_isSharedCheck_2754_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2667_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2754_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2672_; lean_object* v_lemmas_2673_; lean_object* v_bvExprCache_2674_; lean_object* v_bvPredCache_2675_; lean_object* v_bvLogicalCache_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2753_; 
v___x_2672_ = lean_st_ref_take(v_a_2652_);
v_lemmas_2673_ = lean_ctor_get(v___x_2672_, 0);
v_bvExprCache_2674_ = lean_ctor_get(v___x_2672_, 1);
v_bvPredCache_2675_ = lean_ctor_get(v___x_2672_, 2);
v_bvLogicalCache_2676_ = lean_ctor_get(v___x_2672_, 3);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2678_ = v___x_2672_;
v_isShared_2679_ = v_isSharedCheck_2753_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_bvLogicalCache_2676_);
lean_inc(v_bvPredCache_2675_);
lean_inc(v_bvExprCache_2674_);
lean_inc(v_lemmas_2673_);
lean_dec(v___x_2672_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2753_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___y_2681_; lean_object* v___y_2690_; lean_object* v_i_2691_; lean_object* v___y_2707_; lean_object* v_i_2708_; lean_object* v___y_2714_; lean_object* v___x_2723_; 
lean_inc_ref(v_e_2650_);
v___x_2723_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_2664_, v___f_2665_, v_bvPredCache_2675_, v_e_2650_);
switch(lean_obj_tag(v___x_2723_))
{
case 0:
{
lean_object* v_index_2724_; lean_object* v_size_2725_; lean_object* v___x_2726_; 
v_index_2724_ = lean_ctor_get(v___x_2723_, 0);
lean_inc(v_index_2724_);
lean_dec_ref_known(v___x_2723_, 3);
v_size_2725_ = lean_ctor_get(v_bvPredCache_2675_, 0);
lean_inc(v_size_2725_);
lean_inc(v_a_2668_);
v___x_2726_ = l_Std_DHashMap_Raw_setEntry___redArg(v_bvPredCache_2675_, v_size_2725_, v_index_2724_, v_e_2650_, v_a_2668_);
lean_dec(v_index_2724_);
v___y_2681_ = v___x_2726_;
goto v___jp_2680_;
}
case 1:
{
lean_object* v_index_2727_; lean_object* v_size_2728_; lean_object* v_keyArray_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; uint8_t v___x_2733_; 
v_index_2727_ = lean_ctor_get(v___x_2723_, 0);
lean_inc(v_index_2727_);
lean_dec_ref_known(v___x_2723_, 1);
v_size_2728_ = lean_ctor_get(v_bvPredCache_2675_, 0);
v_keyArray_2729_ = lean_ctor_get(v_bvPredCache_2675_, 1);
v___x_2730_ = lean_unsigned_to_nat(1u);
v___x_2731_ = lean_nat_add(v_size_2728_, v___x_2730_);
v___x_2732_ = lean_array_get_size(v_keyArray_2729_);
v___x_2733_ = lean_nat_dec_lt(v___x_2731_, v___x_2732_);
if (v___x_2733_ == 0)
{
lean_dec(v___x_2731_);
lean_dec(v_index_2727_);
goto v___jp_2696_;
}
else
{
lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; uint8_t v___x_2738_; 
v___x_2734_ = lean_unsigned_to_nat(4u);
v___x_2735_ = lean_nat_mul(v___x_2731_, v___x_2734_);
v___x_2736_ = lean_unsigned_to_nat(3u);
v___x_2737_ = lean_nat_mul(v___x_2732_, v___x_2736_);
v___x_2738_ = lean_nat_dec_le(v___x_2735_, v___x_2737_);
lean_dec(v___x_2737_);
lean_dec(v___x_2735_);
if (v___x_2738_ == 0)
{
lean_dec(v___x_2731_);
lean_dec(v_index_2727_);
goto v___jp_2696_;
}
else
{
lean_object* v___x_2739_; 
lean_inc(v_a_2668_);
v___x_2739_ = l_Std_DHashMap_Raw_setEntry___redArg(v_bvPredCache_2675_, v___x_2731_, v_index_2727_, v_e_2650_, v_a_2668_);
lean_dec(v_index_2727_);
v___y_2681_ = v___x_2739_;
goto v___jp_2680_;
}
}
}
default: 
{
lean_object* v_size_2740_; lean_object* v_keyArray_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; uint8_t v___x_2745_; 
v_size_2740_ = lean_ctor_get(v_bvPredCache_2675_, 0);
v_keyArray_2741_ = lean_ctor_get(v_bvPredCache_2675_, 1);
v___x_2742_ = lean_unsigned_to_nat(1u);
v___x_2743_ = lean_nat_add(v_size_2740_, v___x_2742_);
v___x_2744_ = lean_array_get_size(v_keyArray_2741_);
v___x_2745_ = lean_nat_dec_lt(v___x_2743_, v___x_2744_);
if (v___x_2745_ == 0)
{
lean_object* v___x_2746_; 
lean_dec(v___x_2743_);
v___x_2746_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_2664_, v___f_2665_, v_bvPredCache_2675_);
v___y_2714_ = v___x_2746_;
goto v___jp_2713_;
}
else
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; uint8_t v___x_2751_; 
v___x_2747_ = lean_unsigned_to_nat(4u);
v___x_2748_ = lean_nat_mul(v___x_2743_, v___x_2747_);
lean_dec(v___x_2743_);
v___x_2749_ = lean_unsigned_to_nat(3u);
v___x_2750_ = lean_nat_mul(v___x_2744_, v___x_2749_);
v___x_2751_ = lean_nat_dec_le(v___x_2748_, v___x_2750_);
lean_dec(v___x_2750_);
lean_dec(v___x_2748_);
if (v___x_2751_ == 0)
{
lean_object* v___x_2752_; 
v___x_2752_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_2664_, v___f_2665_, v_bvPredCache_2675_);
v___y_2714_ = v___x_2752_;
goto v___jp_2713_;
}
else
{
v___y_2714_ = v_bvPredCache_2675_;
goto v___jp_2713_;
}
}
}
}
v___jp_2680_:
{
lean_object* v___x_2683_; 
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 2, v___y_2681_);
v___x_2683_ = v___x_2678_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_lemmas_2673_);
lean_ctor_set(v_reuseFailAlloc_2688_, 1, v_bvExprCache_2674_);
lean_ctor_set(v_reuseFailAlloc_2688_, 2, v___y_2681_);
lean_ctor_set(v_reuseFailAlloc_2688_, 3, v_bvLogicalCache_2676_);
v___x_2683_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
lean_object* v___x_2684_; lean_object* v___x_2686_; 
v___x_2684_ = lean_st_ref_put(v_a_2652_, v___x_2683_);
if (v_isShared_2671_ == 0)
{
v___x_2686_ = v___x_2670_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_a_2668_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
v___jp_2689_:
{
lean_object* v_size_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v_size_2692_ = lean_ctor_get(v___y_2690_, 0);
v___x_2693_ = lean_unsigned_to_nat(1u);
v___x_2694_ = lean_nat_add(v_size_2692_, v___x_2693_);
lean_inc(v_a_2668_);
v___x_2695_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2690_, v___x_2694_, v_i_2691_, v_e_2650_, v_a_2668_);
lean_dec(v_i_2691_);
v___y_2681_ = v___x_2695_;
goto v___jp_2680_;
}
v___jp_2696_:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2697_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_2664_, v___f_2665_, v_bvPredCache_2675_);
lean_inc_ref(v_e_2650_);
v___x_2698_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_2664_, v___f_2665_, v___x_2697_, v_e_2650_);
switch(lean_obj_tag(v___x_2698_))
{
case 0:
{
lean_object* v_index_2699_; lean_object* v_size_2700_; lean_object* v___x_2701_; 
v_index_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_index_2699_);
lean_dec_ref_known(v___x_2698_, 3);
v_size_2700_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_size_2700_);
lean_inc(v_a_2668_);
v___x_2701_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2697_, v_size_2700_, v_index_2699_, v_e_2650_, v_a_2668_);
lean_dec(v_index_2699_);
v___y_2681_ = v___x_2701_;
goto v___jp_2680_;
}
case 1:
{
lean_object* v_index_2702_; 
v_index_2702_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_index_2702_);
lean_dec_ref_known(v___x_2698_, 1);
v___y_2690_ = v___x_2697_;
v_i_2691_ = v_index_2702_;
goto v___jp_2689_;
}
default: 
{
lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2703_ = lean_unsigned_to_nat(0u);
v___x_2704_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2697_, v___x_2703_);
if (lean_obj_tag(v___x_2704_) == 0)
{
lean_object* v_index_2705_; 
v_index_2705_ = lean_ctor_get(v___x_2704_, 0);
lean_inc(v_index_2705_);
lean_dec_ref_known(v___x_2704_, 1);
v___y_2690_ = v___x_2697_;
v_i_2691_ = v_index_2705_;
goto v___jp_2689_;
}
else
{
lean_dec_ref(v_e_2650_);
v___y_2681_ = v___x_2697_;
goto v___jp_2680_;
}
}
}
}
v___jp_2706_:
{
lean_object* v_size_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v_size_2709_ = lean_ctor_get(v___y_2707_, 0);
v___x_2710_ = lean_unsigned_to_nat(1u);
v___x_2711_ = lean_nat_add(v_size_2709_, v___x_2710_);
lean_inc(v_a_2668_);
v___x_2712_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2707_, v___x_2711_, v_i_2708_, v_e_2650_, v_a_2668_);
lean_dec(v_i_2708_);
v___y_2681_ = v___x_2712_;
goto v___jp_2680_;
}
v___jp_2713_:
{
lean_object* v___x_2715_; 
lean_inc_ref(v_e_2650_);
v___x_2715_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_2664_, v___f_2665_, v___y_2714_, v_e_2650_);
switch(lean_obj_tag(v___x_2715_))
{
case 0:
{
lean_object* v_index_2716_; lean_object* v_size_2717_; lean_object* v___x_2718_; 
v_index_2716_ = lean_ctor_get(v___x_2715_, 0);
lean_inc(v_index_2716_);
lean_dec_ref_known(v___x_2715_, 3);
v_size_2717_ = lean_ctor_get(v___y_2714_, 0);
lean_inc(v_size_2717_);
lean_inc(v_a_2668_);
v___x_2718_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2714_, v_size_2717_, v_index_2716_, v_e_2650_, v_a_2668_);
lean_dec(v_index_2716_);
v___y_2681_ = v___x_2718_;
goto v___jp_2680_;
}
case 1:
{
lean_object* v_index_2719_; 
v_index_2719_ = lean_ctor_get(v___x_2715_, 0);
lean_inc(v_index_2719_);
lean_dec_ref_known(v___x_2715_, 1);
v___y_2707_ = v___y_2714_;
v_i_2708_ = v_index_2719_;
goto v___jp_2706_;
}
default: 
{
lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2720_ = lean_unsigned_to_nat(0u);
v___x_2721_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2714_, v___x_2720_);
if (lean_obj_tag(v___x_2721_) == 0)
{
lean_object* v_index_2722_; 
v_index_2722_ = lean_ctor_get(v___x_2721_, 0);
lean_inc(v_index_2722_);
lean_dec_ref_known(v___x_2721_, 1);
v___y_2707_ = v___y_2714_;
v_i_2708_ = v_index_2722_;
goto v___jp_2706_;
}
else
{
lean_dec_ref(v_e_2650_);
v___y_2681_ = v___y_2714_;
goto v___jp_2680_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2650_);
return v___x_2667_;
}
}
else
{
lean_object* v_val_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
lean_dec_ref(v_f_2651_);
lean_dec_ref(v_e_2650_);
v_val_2755_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2666_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_val_2755_);
lean_dec(v___x_2666_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2760_; 
if (v_isShared_2758_ == 0)
{
lean_ctor_set_tag(v___x_2757_, 0);
v___x_2760_ = v___x_2757_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_val_2755_);
v___x_2760_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
return v___x_2760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache___boxed(lean_object* v_e_2763_, lean_object* v_f_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache(v_e_2763_, v_f_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_);
lean_dec(v_a_2773_);
lean_dec_ref(v_a_2772_);
lean_dec(v_a_2771_);
lean_dec_ref(v_a_2770_);
lean_dec(v_a_2769_);
lean_dec_ref(v_a_2768_);
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2766_);
lean_dec(v_a_2765_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache(lean_object* v_e_2776_, lean_object* v_f_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_){
_start:
{
lean_object* v___x_2788_; lean_object* v_bvLogicalCache_2789_; lean_object* v___f_2790_; lean_object* v___f_2791_; lean_object* v___x_2792_; 
v___x_2788_ = lean_st_ref_get(v_a_2778_);
v_bvLogicalCache_2789_ = lean_ctor_get(v___x_2788_, 3);
lean_inc_ref(v_bvLogicalCache_2789_);
lean_dec(v___x_2788_);
v___f_2790_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__0));
v___f_2791_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__1));
lean_inc_ref(v_e_2776_);
v___x_2792_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_2790_, v___f_2791_, v_bvLogicalCache_2789_, v_e_2776_);
lean_dec_ref(v_bvLogicalCache_2789_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v___x_2793_; 
lean_inc(v_a_2786_);
lean_inc_ref(v_a_2785_);
lean_inc(v_a_2784_);
lean_inc_ref(v_a_2783_);
lean_inc(v_a_2782_);
lean_inc_ref(v_a_2781_);
lean_inc(v_a_2780_);
lean_inc_ref(v_a_2779_);
lean_inc(v_a_2778_);
lean_inc_ref(v_e_2776_);
v___x_2793_ = lean_apply_11(v_f_2777_, v_e_2776_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, lean_box(0));
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2880_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2796_ = v___x_2793_;
v_isShared_2797_ = v_isSharedCheck_2880_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2793_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2880_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2798_; lean_object* v_lemmas_2799_; lean_object* v_bvExprCache_2800_; lean_object* v_bvPredCache_2801_; lean_object* v_bvLogicalCache_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2879_; 
v___x_2798_ = lean_st_ref_take(v_a_2778_);
v_lemmas_2799_ = lean_ctor_get(v___x_2798_, 0);
v_bvExprCache_2800_ = lean_ctor_get(v___x_2798_, 1);
v_bvPredCache_2801_ = lean_ctor_get(v___x_2798_, 2);
v_bvLogicalCache_2802_ = lean_ctor_get(v___x_2798_, 3);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2804_ = v___x_2798_;
v_isShared_2805_ = v_isSharedCheck_2879_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_bvLogicalCache_2802_);
lean_inc(v_bvPredCache_2801_);
lean_inc(v_bvExprCache_2800_);
lean_inc(v_lemmas_2799_);
lean_dec(v___x_2798_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2879_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___y_2807_; lean_object* v___y_2816_; lean_object* v_i_2817_; lean_object* v___y_2833_; lean_object* v_i_2834_; lean_object* v___y_2840_; lean_object* v___x_2849_; 
lean_inc_ref(v_e_2776_);
v___x_2849_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_2790_, v___f_2791_, v_bvLogicalCache_2802_, v_e_2776_);
switch(lean_obj_tag(v___x_2849_))
{
case 0:
{
lean_object* v_index_2850_; lean_object* v_size_2851_; lean_object* v___x_2852_; 
v_index_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_index_2850_);
lean_dec_ref_known(v___x_2849_, 3);
v_size_2851_ = lean_ctor_get(v_bvLogicalCache_2802_, 0);
lean_inc(v_size_2851_);
lean_inc(v_a_2794_);
v___x_2852_ = l_Std_DHashMap_Raw_setEntry___redArg(v_bvLogicalCache_2802_, v_size_2851_, v_index_2850_, v_e_2776_, v_a_2794_);
lean_dec(v_index_2850_);
v___y_2807_ = v___x_2852_;
goto v___jp_2806_;
}
case 1:
{
lean_object* v_index_2853_; lean_object* v_size_2854_; lean_object* v_keyArray_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; uint8_t v___x_2859_; 
v_index_2853_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_index_2853_);
lean_dec_ref_known(v___x_2849_, 1);
v_size_2854_ = lean_ctor_get(v_bvLogicalCache_2802_, 0);
v_keyArray_2855_ = lean_ctor_get(v_bvLogicalCache_2802_, 1);
v___x_2856_ = lean_unsigned_to_nat(1u);
v___x_2857_ = lean_nat_add(v_size_2854_, v___x_2856_);
v___x_2858_ = lean_array_get_size(v_keyArray_2855_);
v___x_2859_ = lean_nat_dec_lt(v___x_2857_, v___x_2858_);
if (v___x_2859_ == 0)
{
lean_dec(v___x_2857_);
lean_dec(v_index_2853_);
goto v___jp_2822_;
}
else
{
lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; uint8_t v___x_2864_; 
v___x_2860_ = lean_unsigned_to_nat(4u);
v___x_2861_ = lean_nat_mul(v___x_2857_, v___x_2860_);
v___x_2862_ = lean_unsigned_to_nat(3u);
v___x_2863_ = lean_nat_mul(v___x_2858_, v___x_2862_);
v___x_2864_ = lean_nat_dec_le(v___x_2861_, v___x_2863_);
lean_dec(v___x_2863_);
lean_dec(v___x_2861_);
if (v___x_2864_ == 0)
{
lean_dec(v___x_2857_);
lean_dec(v_index_2853_);
goto v___jp_2822_;
}
else
{
lean_object* v___x_2865_; 
lean_inc(v_a_2794_);
v___x_2865_ = l_Std_DHashMap_Raw_setEntry___redArg(v_bvLogicalCache_2802_, v___x_2857_, v_index_2853_, v_e_2776_, v_a_2794_);
lean_dec(v_index_2853_);
v___y_2807_ = v___x_2865_;
goto v___jp_2806_;
}
}
}
default: 
{
lean_object* v_size_2866_; lean_object* v_keyArray_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; uint8_t v___x_2871_; 
v_size_2866_ = lean_ctor_get(v_bvLogicalCache_2802_, 0);
v_keyArray_2867_ = lean_ctor_get(v_bvLogicalCache_2802_, 1);
v___x_2868_ = lean_unsigned_to_nat(1u);
v___x_2869_ = lean_nat_add(v_size_2866_, v___x_2868_);
v___x_2870_ = lean_array_get_size(v_keyArray_2867_);
v___x_2871_ = lean_nat_dec_lt(v___x_2869_, v___x_2870_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; 
lean_dec(v___x_2869_);
v___x_2872_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_2790_, v___f_2791_, v_bvLogicalCache_2802_);
v___y_2840_ = v___x_2872_;
goto v___jp_2839_;
}
else
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; uint8_t v___x_2877_; 
v___x_2873_ = lean_unsigned_to_nat(4u);
v___x_2874_ = lean_nat_mul(v___x_2869_, v___x_2873_);
lean_dec(v___x_2869_);
v___x_2875_ = lean_unsigned_to_nat(3u);
v___x_2876_ = lean_nat_mul(v___x_2870_, v___x_2875_);
v___x_2877_ = lean_nat_dec_le(v___x_2874_, v___x_2876_);
lean_dec(v___x_2876_);
lean_dec(v___x_2874_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2878_; 
v___x_2878_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_2790_, v___f_2791_, v_bvLogicalCache_2802_);
v___y_2840_ = v___x_2878_;
goto v___jp_2839_;
}
else
{
v___y_2840_ = v_bvLogicalCache_2802_;
goto v___jp_2839_;
}
}
}
}
v___jp_2806_:
{
lean_object* v___x_2809_; 
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 3, v___y_2807_);
v___x_2809_ = v___x_2804_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_lemmas_2799_);
lean_ctor_set(v_reuseFailAlloc_2814_, 1, v_bvExprCache_2800_);
lean_ctor_set(v_reuseFailAlloc_2814_, 2, v_bvPredCache_2801_);
lean_ctor_set(v_reuseFailAlloc_2814_, 3, v___y_2807_);
v___x_2809_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
lean_object* v___x_2810_; lean_object* v___x_2812_; 
v___x_2810_ = lean_st_ref_put(v_a_2778_, v___x_2809_);
if (v_isShared_2797_ == 0)
{
v___x_2812_ = v___x_2796_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2813_; 
v_reuseFailAlloc_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2813_, 0, v_a_2794_);
v___x_2812_ = v_reuseFailAlloc_2813_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
return v___x_2812_;
}
}
}
v___jp_2815_:
{
lean_object* v_size_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v_size_2818_ = lean_ctor_get(v___y_2816_, 0);
v___x_2819_ = lean_unsigned_to_nat(1u);
v___x_2820_ = lean_nat_add(v_size_2818_, v___x_2819_);
lean_inc(v_a_2794_);
v___x_2821_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2816_, v___x_2820_, v_i_2817_, v_e_2776_, v_a_2794_);
lean_dec(v_i_2817_);
v___y_2807_ = v___x_2821_;
goto v___jp_2806_;
}
v___jp_2822_:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2823_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_2790_, v___f_2791_, v_bvLogicalCache_2802_);
lean_inc_ref(v_e_2776_);
v___x_2824_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_2790_, v___f_2791_, v___x_2823_, v_e_2776_);
switch(lean_obj_tag(v___x_2824_))
{
case 0:
{
lean_object* v_index_2825_; lean_object* v_size_2826_; lean_object* v___x_2827_; 
v_index_2825_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_index_2825_);
lean_dec_ref_known(v___x_2824_, 3);
v_size_2826_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_size_2826_);
lean_inc(v_a_2794_);
v___x_2827_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2823_, v_size_2826_, v_index_2825_, v_e_2776_, v_a_2794_);
lean_dec(v_index_2825_);
v___y_2807_ = v___x_2827_;
goto v___jp_2806_;
}
case 1:
{
lean_object* v_index_2828_; 
v_index_2828_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_index_2828_);
lean_dec_ref_known(v___x_2824_, 1);
v___y_2816_ = v___x_2823_;
v_i_2817_ = v_index_2828_;
goto v___jp_2815_;
}
default: 
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2829_ = lean_unsigned_to_nat(0u);
v___x_2830_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2823_, v___x_2829_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_index_2831_; 
v_index_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_index_2831_);
lean_dec_ref_known(v___x_2830_, 1);
v___y_2816_ = v___x_2823_;
v_i_2817_ = v_index_2831_;
goto v___jp_2815_;
}
else
{
lean_dec_ref(v_e_2776_);
v___y_2807_ = v___x_2823_;
goto v___jp_2806_;
}
}
}
}
v___jp_2832_:
{
lean_object* v_size_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v_size_2835_ = lean_ctor_get(v___y_2833_, 0);
v___x_2836_ = lean_unsigned_to_nat(1u);
v___x_2837_ = lean_nat_add(v_size_2835_, v___x_2836_);
lean_inc(v_a_2794_);
v___x_2838_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2833_, v___x_2837_, v_i_2834_, v_e_2776_, v_a_2794_);
lean_dec(v_i_2834_);
v___y_2807_ = v___x_2838_;
goto v___jp_2806_;
}
v___jp_2839_:
{
lean_object* v___x_2841_; 
lean_inc_ref(v_e_2776_);
v___x_2841_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_2790_, v___f_2791_, v___y_2840_, v_e_2776_);
switch(lean_obj_tag(v___x_2841_))
{
case 0:
{
lean_object* v_index_2842_; lean_object* v_size_2843_; lean_object* v___x_2844_; 
v_index_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_index_2842_);
lean_dec_ref_known(v___x_2841_, 3);
v_size_2843_ = lean_ctor_get(v___y_2840_, 0);
lean_inc(v_size_2843_);
lean_inc(v_a_2794_);
v___x_2844_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2840_, v_size_2843_, v_index_2842_, v_e_2776_, v_a_2794_);
lean_dec(v_index_2842_);
v___y_2807_ = v___x_2844_;
goto v___jp_2806_;
}
case 1:
{
lean_object* v_index_2845_; 
v_index_2845_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_index_2845_);
lean_dec_ref_known(v___x_2841_, 1);
v___y_2833_ = v___y_2840_;
v_i_2834_ = v_index_2845_;
goto v___jp_2832_;
}
default: 
{
lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2846_ = lean_unsigned_to_nat(0u);
v___x_2847_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2840_, v___x_2846_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v_index_2848_; 
v_index_2848_ = lean_ctor_get(v___x_2847_, 0);
lean_inc(v_index_2848_);
lean_dec_ref_known(v___x_2847_, 1);
v___y_2833_ = v___y_2840_;
v_i_2834_ = v_index_2848_;
goto v___jp_2832_;
}
else
{
lean_dec_ref(v_e_2776_);
v___y_2807_ = v___y_2840_;
goto v___jp_2806_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_2776_);
return v___x_2793_;
}
}
else
{
lean_object* v_val_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2888_; 
lean_dec_ref(v_f_2777_);
lean_dec_ref(v_e_2776_);
v_val_2881_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2883_ = v___x_2792_;
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_val_2881_);
lean_dec(v___x_2792_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2886_; 
if (v_isShared_2884_ == 0)
{
lean_ctor_set_tag(v___x_2883_, 0);
v___x_2886_ = v___x_2883_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_val_2881_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___boxed(lean_object* v_e_2889_, lean_object* v_f_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache(v_e_2889_, v_f_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_);
lean_dec(v_a_2899_);
lean_dec_ref(v_a_2898_);
lean_dec(v_a_2897_);
lean_dec_ref(v_a_2896_);
lean_dec(v_a_2895_);
lean_dec_ref(v_a_2894_);
lean_dec(v_a_2893_);
lean_dec_ref(v_a_2892_);
lean_dec(v_a_2891_);
return v_res_2901_;
}
}
lean_object* runtime_initialize_Std_Data_HashMap(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_RArray(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp = _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp);
l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp = _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp);
l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred = _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred);
l_Lean_Meta_Tactic_BVDecide_instToExprGate = _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_instToExprGate);
l_Lean_Meta_Tactic_BVDecide_instToExprBVPred = _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVPred();
lean_mark_persistent(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_HashMap(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* initialize_Lean_Data_RArray(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_RArray(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Reflect_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
