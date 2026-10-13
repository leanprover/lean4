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
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
size_t lean_ptr_addr(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_RArray_ofArray___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RArray_toExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofBool"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__7_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 35, 113, 77, 117, 41, 40, 246)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_FunAtom_atomExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_FunAtom_atomExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_evalsAtAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_evalsAtAtoms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_run_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_run_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__1;
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__2_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__2_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__2_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_run_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_run_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atoms___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atoms___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atoms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__3_spec__6_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__0(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__3_spec__6_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "updateAtomsAssignment should only be called when there is an atom"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PackedBitVec"};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 161, 28, 104, 237, 118, 82, 71)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(160, 152, 89, 246, 197, 180, 246, 240)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 53, 240, 176, 234, 207, 251, 199)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__2_value),LEAN_SCALAR_PTR_LITERAL(53, 26, 122, 246, 246, 235, 136, 91)}};
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___lam__0, .m_arity = 7, .m_num_fixed = 6, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__0_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__2_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__0_value),((lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_ReifyM_isAtom_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_ReifyM_isAtom_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_isAtom___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_isAtom___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_isAtom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_isAtom___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_ReifyM_isAtom_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_ReifyM_isAtom_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_getAtomNumber___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_getAtomNumber___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_getAtomNumber(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_getAtomNumber___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___closed__0;
static const lean_closure_object l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__0_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__1_value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__2_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__5;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "New atom of width "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__7;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = ", synthetic\? "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__8 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__9;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__10 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__11;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Meta.Tactic.BVDecide.Reflect.Basic"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__12 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__12_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Meta.Tactic.BVDecide.ReifyM.lookup"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__13 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__13_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "The same atom occurs with different widths, this is a bug"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__14 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__15;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_modifyTheoryState___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_modifyTheoryState___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_modifyTheoryState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_modifyTheoryState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyBinaryProof_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyBinaryProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyTernaryProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_getHyps___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_getHyps___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_getHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_getHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_getLemmas___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_getLemmas___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_getLemmas(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_getLemmas___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instBEqExprPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_instHashableExprPtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper___closed__2(void){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_751_ = lean_box(0);
v___x_752_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper___closed__1));
v___x_753_ = l_Lean_mkConst(v___x_752_, v___x_751_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper(lean_object* v_e_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_762_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper___closed__2, &l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper___closed__2);
v___x_763_ = l_Lean_Expr_app___override(v___x_762_, v_e_754_);
v___x_764_ = l_Lean_Meta_Sym_shareCommonInc(v___x_763_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper___boxed(lean_object* v_e_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper(v_e_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_);
lean_dec(v_a_771_);
lean_dec_ref(v_a_770_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_FunAtom_atomExpr(lean_object* v_funAtom_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
uint8_t v_isBoolAtom_782_; 
v_isBoolAtom_782_ = lean_ctor_get_uint8(v_funAtom_774_, sizeof(void*)*1);
if (v_isBoolAtom_782_ == 0)
{
lean_object* v_funExpr_783_; lean_object* v___x_784_; 
v_funExpr_783_ = lean_ctor_get(v_funAtom_774_, 0);
lean_inc_ref(v_funExpr_783_);
lean_dec_ref(v_funAtom_774_);
v___x_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_784_, 0, v_funExpr_783_);
return v___x_784_;
}
else
{
lean_object* v_funExpr_785_; lean_object* v___x_786_; 
v_funExpr_785_ = lean_ctor_get(v_funAtom_774_, 0);
lean_inc_ref(v_funExpr_785_);
lean_dec_ref(v_funAtom_774_);
v___x_786_ = l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper(v_funExpr_785_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
return v___x_786_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_FunAtom_atomExpr___boxed(lean_object* v_funAtom_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Lean_Meta_Tactic_BVDecide_FunAtom_atomExpr(v_funAtom_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
lean_dec(v_a_791_);
lean_dec_ref(v_a_790_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
return v_res_795_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg(lean_object* v_a_796_, lean_object* v_x_797_){
_start:
{
if (lean_obj_tag(v_x_797_) == 0)
{
uint8_t v___x_798_; 
v___x_798_ = 0;
return v___x_798_;
}
else
{
lean_object* v_key_799_; lean_object* v_tail_800_; size_t v___x_801_; size_t v___x_802_; uint8_t v___x_803_; 
v_key_799_ = lean_ctor_get(v_x_797_, 0);
v_tail_800_ = lean_ctor_get(v_x_797_, 2);
v___x_801_ = lean_ptr_addr(v_key_799_);
v___x_802_ = lean_ptr_addr(v_a_796_);
v___x_803_ = lean_usize_dec_eq(v___x_801_, v___x_802_);
if (v___x_803_ == 0)
{
v_x_797_ = v_tail_800_;
goto _start;
}
else
{
return v___x_803_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg___boxed(lean_object* v_a_805_, lean_object* v_x_806_){
_start:
{
uint8_t v_res_807_; lean_object* v_r_808_; 
v_res_807_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg(v_a_805_, v_x_806_);
lean_dec(v_x_806_);
lean_dec_ref(v_a_805_);
v_r_808_ = lean_box(v_res_807_);
return v_r_808_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_809_, lean_object* v_x_810_){
_start:
{
if (lean_obj_tag(v_x_810_) == 0)
{
return v_x_809_;
}
else
{
lean_object* v_key_811_; lean_object* v_value_812_; lean_object* v_tail_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_839_; 
v_key_811_ = lean_ctor_get(v_x_810_, 0);
v_value_812_ = lean_ctor_get(v_x_810_, 1);
v_tail_813_ = lean_ctor_get(v_x_810_, 2);
v_isSharedCheck_839_ = !lean_is_exclusive(v_x_810_);
if (v_isSharedCheck_839_ == 0)
{
v___x_815_ = v_x_810_;
v_isShared_816_ = v_isSharedCheck_839_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_tail_813_);
lean_inc(v_value_812_);
lean_inc(v_key_811_);
lean_dec(v_x_810_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_839_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_817_; size_t v___x_818_; size_t v___x_819_; size_t v___x_820_; uint64_t v___x_821_; uint64_t v___x_822_; uint64_t v___x_823_; uint64_t v_fold_824_; uint64_t v___x_825_; uint64_t v___x_826_; uint64_t v___x_827_; size_t v___x_828_; size_t v___x_829_; size_t v___x_830_; size_t v___x_831_; size_t v___x_832_; lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_817_ = lean_array_get_size(v_x_809_);
v___x_818_ = lean_ptr_addr(v_key_811_);
v___x_819_ = ((size_t)3ULL);
v___x_820_ = lean_usize_shift_right(v___x_818_, v___x_819_);
v___x_821_ = lean_usize_to_uint64(v___x_820_);
v___x_822_ = 32ULL;
v___x_823_ = lean_uint64_shift_right(v___x_821_, v___x_822_);
v_fold_824_ = lean_uint64_xor(v___x_821_, v___x_823_);
v___x_825_ = 16ULL;
v___x_826_ = lean_uint64_shift_right(v_fold_824_, v___x_825_);
v___x_827_ = lean_uint64_xor(v_fold_824_, v___x_826_);
v___x_828_ = lean_uint64_to_usize(v___x_827_);
v___x_829_ = lean_usize_of_nat(v___x_817_);
v___x_830_ = ((size_t)1ULL);
v___x_831_ = lean_usize_sub(v___x_829_, v___x_830_);
v___x_832_ = lean_usize_land(v___x_828_, v___x_831_);
v___x_833_ = lean_array_uget_borrowed(v_x_809_, v___x_832_);
lean_inc(v___x_833_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 2, v___x_833_);
v___x_835_ = v___x_815_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_key_811_);
lean_ctor_set(v_reuseFailAlloc_838_, 1, v_value_812_);
lean_ctor_set(v_reuseFailAlloc_838_, 2, v___x_833_);
v___x_835_ = v_reuseFailAlloc_838_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
lean_object* v___x_836_; 
v___x_836_ = lean_array_uset(v_x_809_, v___x_832_, v___x_835_);
v_x_809_ = v___x_836_;
v_x_810_ = v_tail_813_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4___redArg(lean_object* v_i_840_, lean_object* v_source_841_, lean_object* v_target_842_){
_start:
{
lean_object* v___x_843_; uint8_t v___x_844_; 
v___x_843_ = lean_array_get_size(v_source_841_);
v___x_844_ = lean_nat_dec_lt(v_i_840_, v___x_843_);
if (v___x_844_ == 0)
{
lean_dec_ref(v_source_841_);
lean_dec(v_i_840_);
return v_target_842_;
}
else
{
lean_object* v_es_845_; lean_object* v___x_846_; lean_object* v_source_847_; lean_object* v_target_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v_es_845_ = lean_array_fget(v_source_841_, v_i_840_);
v___x_846_ = lean_box(0);
v_source_847_ = lean_array_fset(v_source_841_, v_i_840_, v___x_846_);
v_target_848_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4_spec__5___redArg(v_target_842_, v_es_845_);
v___x_849_ = lean_unsigned_to_nat(1u);
v___x_850_ = lean_nat_add(v_i_840_, v___x_849_);
lean_dec(v_i_840_);
v_i_840_ = v___x_850_;
v_source_841_ = v_source_847_;
v_target_842_ = v_target_848_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3___redArg(lean_object* v_data_852_){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v_nbuckets_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_853_ = lean_array_get_size(v_data_852_);
v___x_854_ = lean_unsigned_to_nat(2u);
v_nbuckets_855_ = lean_nat_mul(v___x_853_, v___x_854_);
v___x_856_ = lean_unsigned_to_nat(0u);
v___x_857_ = lean_box(0);
v___x_858_ = lean_mk_array(v_nbuckets_855_, v___x_857_);
v___x_859_ = lean_array_propagate_mark(v_data_852_, v___x_858_);
v___x_860_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4___redArg(v___x_856_, v_data_852_, v___x_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__4___redArg(lean_object* v_a_861_, lean_object* v_b_862_, lean_object* v_x_863_){
_start:
{
if (lean_obj_tag(v_x_863_) == 0)
{
lean_dec(v_b_862_);
lean_dec_ref(v_a_861_);
return v_x_863_;
}
else
{
lean_object* v_key_864_; lean_object* v_value_865_; lean_object* v_tail_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_880_; 
v_key_864_ = lean_ctor_get(v_x_863_, 0);
v_value_865_ = lean_ctor_get(v_x_863_, 1);
v_tail_866_ = lean_ctor_get(v_x_863_, 2);
v_isSharedCheck_880_ = !lean_is_exclusive(v_x_863_);
if (v_isSharedCheck_880_ == 0)
{
v___x_868_ = v_x_863_;
v_isShared_869_ = v_isSharedCheck_880_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_tail_866_);
lean_inc(v_value_865_);
lean_inc(v_key_864_);
lean_dec(v_x_863_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_880_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
size_t v___x_870_; size_t v___x_871_; uint8_t v___x_872_; 
v___x_870_ = lean_ptr_addr(v_key_864_);
v___x_871_ = lean_ptr_addr(v_a_861_);
v___x_872_ = lean_usize_dec_eq(v___x_870_, v___x_871_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; lean_object* v___x_875_; 
v___x_873_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__4___redArg(v_a_861_, v_b_862_, v_tail_866_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 2, v___x_873_);
v___x_875_ = v___x_868_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_key_864_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_value_865_);
lean_ctor_set(v_reuseFailAlloc_876_, 2, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
else
{
lean_object* v___x_878_; 
lean_dec(v_value_865_);
lean_dec(v_key_864_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 1, v_b_862_);
lean_ctor_set(v___x_868_, 0, v_a_861_);
v___x_878_ = v___x_868_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_861_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_b_862_);
lean_ctor_set(v_reuseFailAlloc_879_, 2, v_tail_866_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(lean_object* v_m_881_, lean_object* v_a_882_, lean_object* v_b_883_){
_start:
{
lean_object* v_size_884_; lean_object* v_buckets_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_931_; 
v_size_884_ = lean_ctor_get(v_m_881_, 0);
v_buckets_885_ = lean_ctor_get(v_m_881_, 1);
v_isSharedCheck_931_ = !lean_is_exclusive(v_m_881_);
if (v_isSharedCheck_931_ == 0)
{
v___x_887_ = v_m_881_;
v_isShared_888_ = v_isSharedCheck_931_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_buckets_885_);
lean_inc(v_size_884_);
lean_dec(v_m_881_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_931_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_889_; size_t v___x_890_; size_t v___x_891_; size_t v___x_892_; uint64_t v___x_893_; uint64_t v___x_894_; uint64_t v___x_895_; uint64_t v_fold_896_; uint64_t v___x_897_; uint64_t v___x_898_; uint64_t v___x_899_; size_t v___x_900_; size_t v___x_901_; size_t v___x_902_; size_t v___x_903_; size_t v___x_904_; lean_object* v_bkt_905_; uint8_t v___x_906_; 
v___x_889_ = lean_array_get_size(v_buckets_885_);
v___x_890_ = lean_ptr_addr(v_a_882_);
v___x_891_ = ((size_t)3ULL);
v___x_892_ = lean_usize_shift_right(v___x_890_, v___x_891_);
v___x_893_ = lean_usize_to_uint64(v___x_892_);
v___x_894_ = 32ULL;
v___x_895_ = lean_uint64_shift_right(v___x_893_, v___x_894_);
v_fold_896_ = lean_uint64_xor(v___x_893_, v___x_895_);
v___x_897_ = 16ULL;
v___x_898_ = lean_uint64_shift_right(v_fold_896_, v___x_897_);
v___x_899_ = lean_uint64_xor(v_fold_896_, v___x_898_);
v___x_900_ = lean_uint64_to_usize(v___x_899_);
v___x_901_ = lean_usize_of_nat(v___x_889_);
v___x_902_ = ((size_t)1ULL);
v___x_903_ = lean_usize_sub(v___x_901_, v___x_902_);
v___x_904_ = lean_usize_land(v___x_900_, v___x_903_);
v_bkt_905_ = lean_array_uget_borrowed(v_buckets_885_, v___x_904_);
v___x_906_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg(v_a_882_, v_bkt_905_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; lean_object* v_size_x27_908_; lean_object* v___x_909_; lean_object* v_buckets_x27_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v___x_907_ = lean_unsigned_to_nat(1u);
v_size_x27_908_ = lean_nat_add(v_size_884_, v___x_907_);
lean_dec(v_size_884_);
lean_inc(v_bkt_905_);
v___x_909_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_909_, 0, v_a_882_);
lean_ctor_set(v___x_909_, 1, v_b_883_);
lean_ctor_set(v___x_909_, 2, v_bkt_905_);
v_buckets_x27_910_ = lean_array_uset(v_buckets_885_, v___x_904_, v___x_909_);
v___x_911_ = lean_unsigned_to_nat(4u);
v___x_912_ = lean_nat_mul(v_size_x27_908_, v___x_911_);
v___x_913_ = lean_unsigned_to_nat(3u);
v___x_914_ = lean_nat_div(v___x_912_, v___x_913_);
lean_dec(v___x_912_);
v___x_915_ = lean_array_get_size(v_buckets_x27_910_);
v___x_916_ = lean_nat_dec_le(v___x_914_, v___x_915_);
lean_dec(v___x_914_);
if (v___x_916_ == 0)
{
lean_object* v_val_917_; lean_object* v___x_919_; 
v_val_917_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3___redArg(v_buckets_x27_910_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 1, v_val_917_);
lean_ctor_set(v___x_887_, 0, v_size_x27_908_);
v___x_919_ = v___x_887_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_size_x27_908_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_val_917_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
else
{
lean_object* v___x_922_; 
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 1, v_buckets_x27_910_);
lean_ctor_set(v___x_887_, 0, v_size_x27_908_);
v___x_922_ = v___x_887_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_size_x27_908_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_buckets_x27_910_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
else
{
lean_object* v___x_924_; lean_object* v_buckets_x27_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_929_; 
lean_inc(v_bkt_905_);
v___x_924_ = lean_box(0);
v_buckets_x27_925_ = lean_array_uset(v_buckets_885_, v___x_904_, v___x_924_);
v___x_926_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__4___redArg(v_a_882_, v_b_883_, v_bkt_905_);
v___x_927_ = lean_array_uset(v_buckets_x27_925_, v___x_904_, v___x_926_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 1, v___x_927_);
v___x_929_ = v___x_887_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_size_884_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v___x_927_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg(lean_object* v_a_932_, lean_object* v_x_933_){
_start:
{
if (lean_obj_tag(v_x_933_) == 0)
{
lean_object* v___x_934_; 
v___x_934_ = lean_box(0);
return v___x_934_;
}
else
{
lean_object* v_key_935_; lean_object* v_value_936_; lean_object* v_tail_937_; size_t v___x_938_; size_t v___x_939_; uint8_t v___x_940_; 
v_key_935_ = lean_ctor_get(v_x_933_, 0);
v_value_936_ = lean_ctor_get(v_x_933_, 1);
v_tail_937_ = lean_ctor_get(v_x_933_, 2);
v___x_938_ = lean_ptr_addr(v_key_935_);
v___x_939_ = lean_ptr_addr(v_a_932_);
v___x_940_ = lean_usize_dec_eq(v___x_938_, v___x_939_);
if (v___x_940_ == 0)
{
v_x_933_ = v_tail_937_;
goto _start;
}
else
{
lean_object* v___x_942_; 
lean_inc(v_value_936_);
v___x_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_942_, 0, v_value_936_);
return v___x_942_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg___boxed(lean_object* v_a_943_, lean_object* v_x_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg(v_a_943_, v_x_944_);
lean_dec(v_x_944_);
lean_dec_ref(v_a_943_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(lean_object* v_m_946_, lean_object* v_a_947_){
_start:
{
lean_object* v_buckets_948_; lean_object* v___x_949_; size_t v___x_950_; size_t v___x_951_; size_t v___x_952_; uint64_t v___x_953_; uint64_t v___x_954_; uint64_t v___x_955_; uint64_t v_fold_956_; uint64_t v___x_957_; uint64_t v___x_958_; uint64_t v___x_959_; size_t v___x_960_; size_t v___x_961_; size_t v___x_962_; size_t v___x_963_; size_t v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v_buckets_948_ = lean_ctor_get(v_m_946_, 1);
v___x_949_ = lean_array_get_size(v_buckets_948_);
v___x_950_ = lean_ptr_addr(v_a_947_);
v___x_951_ = ((size_t)3ULL);
v___x_952_ = lean_usize_shift_right(v___x_950_, v___x_951_);
v___x_953_ = lean_usize_to_uint64(v___x_952_);
v___x_954_ = 32ULL;
v___x_955_ = lean_uint64_shift_right(v___x_953_, v___x_954_);
v_fold_956_ = lean_uint64_xor(v___x_953_, v___x_955_);
v___x_957_ = 16ULL;
v___x_958_ = lean_uint64_shift_right(v_fold_956_, v___x_957_);
v___x_959_ = lean_uint64_xor(v_fold_956_, v___x_958_);
v___x_960_ = lean_uint64_to_usize(v___x_959_);
v___x_961_ = lean_usize_of_nat(v___x_949_);
v___x_962_ = ((size_t)1ULL);
v___x_963_ = lean_usize_sub(v___x_961_, v___x_962_);
v___x_964_ = lean_usize_land(v___x_960_, v___x_963_);
v___x_965_ = lean_array_uget_borrowed(v_buckets_948_, v___x_964_);
v___x_966_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg(v_a_947_, v___x_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg___boxed(lean_object* v_m_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_m_967_, v_a_968_);
lean_dec_ref(v_a_968_);
lean_dec_ref(v_m_967_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(lean_object* v_reified_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_){
_start:
{
lean_object* v_originalExpr_983_; lean_object* v_evalsAtAtoms_x27_984_; lean_object* v___x_985_; lean_object* v_evalsAtCache_986_; lean_object* v___x_987_; 
v_originalExpr_983_ = lean_ctor_get(v_reified_970_, 2);
lean_inc_ref(v_originalExpr_983_);
v_evalsAtAtoms_x27_984_ = lean_ctor_get(v_reified_970_, 3);
lean_inc_ref(v_evalsAtAtoms_x27_984_);
lean_dec_ref(v_reified_970_);
v___x_985_ = lean_st_ref_get(v_a_972_);
v_evalsAtCache_986_ = lean_ctor_get(v___x_985_, 3);
lean_inc_ref(v_evalsAtCache_986_);
lean_dec(v___x_985_);
v___x_987_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_evalsAtCache_986_, v_originalExpr_983_);
lean_dec_ref(v_evalsAtCache_986_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v___x_988_; 
lean_inc(v_a_981_);
lean_inc_ref(v_a_980_);
lean_inc(v_a_979_);
lean_inc_ref(v_a_978_);
lean_inc(v_a_977_);
lean_inc_ref(v_a_976_);
lean_inc(v_a_975_);
lean_inc_ref(v_a_974_);
lean_inc(v_a_973_);
lean_inc(v_a_972_);
lean_inc_ref(v_a_971_);
v___x_988_ = lean_apply_12(v_evalsAtAtoms_x27_984_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, lean_box(0));
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1011_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_991_ = v___x_988_;
v_isShared_992_ = v_isSharedCheck_1011_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_988_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1011_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_993_; lean_object* v_atoms_994_; lean_object* v_atomsAssignmentExprCache_995_; lean_object* v_atomsAssignmentMapCache_996_; lean_object* v_evalsAtCache_997_; lean_object* v_theoryState_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1010_; 
v___x_993_ = lean_st_ref_take(v_a_972_);
v_atoms_994_ = lean_ctor_get(v___x_993_, 0);
v_atomsAssignmentExprCache_995_ = lean_ctor_get(v___x_993_, 1);
v_atomsAssignmentMapCache_996_ = lean_ctor_get(v___x_993_, 2);
v_evalsAtCache_997_ = lean_ctor_get(v___x_993_, 3);
v_theoryState_998_ = lean_ctor_get(v___x_993_, 4);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1000_ = v___x_993_;
v_isShared_1001_ = v_isSharedCheck_1010_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_theoryState_998_);
lean_inc(v_evalsAtCache_997_);
lean_inc(v_atomsAssignmentMapCache_996_);
lean_inc(v_atomsAssignmentExprCache_995_);
lean_inc(v_atoms_994_);
lean_dec(v___x_993_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1010_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1002_; lean_object* v___x_1004_; 
lean_inc(v_a_989_);
v___x_1002_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v_evalsAtCache_997_, v_originalExpr_983_, v_a_989_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 3, v___x_1002_);
v___x_1004_ = v___x_1000_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_atoms_994_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_atomsAssignmentExprCache_995_);
lean_ctor_set(v_reuseFailAlloc_1009_, 2, v_atomsAssignmentMapCache_996_);
lean_ctor_set(v_reuseFailAlloc_1009_, 3, v___x_1002_);
lean_ctor_set(v_reuseFailAlloc_1009_, 4, v_theoryState_998_);
v___x_1004_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
lean_object* v___x_1005_; lean_object* v___x_1007_; 
v___x_1005_ = lean_st_ref_put(v_a_972_, v___x_1004_);
if (v_isShared_992_ == 0)
{
v___x_1007_ = v___x_991_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_989_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
}
else
{
lean_dec_ref(v_originalExpr_983_);
return v___x_988_;
}
}
else
{
lean_object* v_val_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
lean_dec_ref(v_evalsAtAtoms_x27_984_);
lean_dec_ref(v_originalExpr_983_);
v_val_1012_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_987_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_val_1012_);
lean_dec(v___x_987_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
lean_ctor_set_tag(v___x_1014_, 0);
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_val_1012_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms___boxed(lean_object* v_reified_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(v_reified_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_);
lean_dec(v_a_1031_);
lean_dec_ref(v_a_1030_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
lean_dec(v_a_1025_);
lean_dec_ref(v_a_1024_);
lean_dec(v_a_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0(lean_object* v_00_u03b2_1034_, lean_object* v_m_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_m_1035_, v_a_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___boxed(lean_object* v_00_u03b2_1038_, lean_object* v_m_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0(v_00_u03b2_1038_, v_m_1039_, v_a_1040_);
lean_dec_ref(v_a_1040_);
lean_dec_ref(v_m_1039_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1(lean_object* v_00_u03b2_1042_, lean_object* v_m_1043_, lean_object* v_a_1044_, lean_object* v_b_1045_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v_m_1043_, v_a_1044_, v_b_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0(lean_object* v_00_u03b2_1047_, lean_object* v_a_1048_, lean_object* v_x_1049_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg(v_a_1048_, v_x_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1051_, lean_object* v_a_1052_, lean_object* v_x_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0(v_00_u03b2_1051_, v_a_1052_, v_x_1053_);
lean_dec(v_x_1053_);
lean_dec_ref(v_a_1052_);
return v_res_1054_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2(lean_object* v_00_u03b2_1055_, lean_object* v_a_1056_, lean_object* v_x_1057_){
_start:
{
uint8_t v___x_1058_; 
v___x_1058_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg(v_a_1056_, v_x_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1059_, lean_object* v_a_1060_, lean_object* v_x_1061_){
_start:
{
uint8_t v_res_1062_; lean_object* v_r_1063_; 
v_res_1062_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2(v_00_u03b2_1059_, v_a_1060_, v_x_1061_);
lean_dec(v_x_1061_);
lean_dec_ref(v_a_1060_);
v_r_1063_ = lean_box(v_res_1062_);
return v_r_1063_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3(lean_object* v_00_u03b2_1064_, lean_object* v_data_1065_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3___redArg(v_data_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__4(lean_object* v_00_u03b2_1067_, lean_object* v_a_1068_, lean_object* v_b_1069_, lean_object* v_x_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__4___redArg(v_a_1068_, v_b_1069_, v_x_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1072_, lean_object* v_i_1073_, lean_object* v_source_1074_, lean_object* v_target_1075_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4___redArg(v_i_1073_, v_source_1074_, v_target_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1077_, lean_object* v_x_1078_, lean_object* v_x_1079_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1078_, v_x_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_evalsAtAtoms(lean_object* v_reified_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v_originalExpr_1094_; lean_object* v_evalsAtAtoms_x27_1095_; lean_object* v___x_1096_; lean_object* v_evalsAtCache_1097_; lean_object* v___x_1098_; 
v_originalExpr_1094_ = lean_ctor_get(v_reified_1081_, 1);
lean_inc_ref(v_originalExpr_1094_);
v_evalsAtAtoms_x27_1095_ = lean_ctor_get(v_reified_1081_, 2);
lean_inc_ref(v_evalsAtAtoms_x27_1095_);
lean_dec_ref(v_reified_1081_);
v___x_1096_ = lean_st_ref_get(v_a_1083_);
v_evalsAtCache_1097_ = lean_ctor_get(v___x_1096_, 3);
lean_inc_ref(v_evalsAtCache_1097_);
lean_dec(v___x_1096_);
v___x_1098_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_evalsAtCache_1097_, v_originalExpr_1094_);
lean_dec_ref(v_evalsAtCache_1097_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v___x_1099_; 
lean_inc(v_a_1092_);
lean_inc_ref(v_a_1091_);
lean_inc(v_a_1090_);
lean_inc_ref(v_a_1089_);
lean_inc(v_a_1088_);
lean_inc_ref(v_a_1087_);
lean_inc(v_a_1086_);
lean_inc_ref(v_a_1085_);
lean_inc(v_a_1084_);
lean_inc(v_a_1083_);
lean_inc_ref(v_a_1082_);
v___x_1099_ = lean_apply_12(v_evalsAtAtoms_x27_1095_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, lean_box(0));
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1122_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1102_ = v___x_1099_;
v_isShared_1103_ = v_isSharedCheck_1122_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1099_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1122_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1104_; lean_object* v_atoms_1105_; lean_object* v_atomsAssignmentExprCache_1106_; lean_object* v_atomsAssignmentMapCache_1107_; lean_object* v_evalsAtCache_1108_; lean_object* v_theoryState_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1121_; 
v___x_1104_ = lean_st_ref_take(v_a_1083_);
v_atoms_1105_ = lean_ctor_get(v___x_1104_, 0);
v_atomsAssignmentExprCache_1106_ = lean_ctor_get(v___x_1104_, 1);
v_atomsAssignmentMapCache_1107_ = lean_ctor_get(v___x_1104_, 2);
v_evalsAtCache_1108_ = lean_ctor_get(v___x_1104_, 3);
v_theoryState_1109_ = lean_ctor_get(v___x_1104_, 4);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1111_ = v___x_1104_;
v_isShared_1112_ = v_isSharedCheck_1121_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_theoryState_1109_);
lean_inc(v_evalsAtCache_1108_);
lean_inc(v_atomsAssignmentMapCache_1107_);
lean_inc(v_atomsAssignmentExprCache_1106_);
lean_inc(v_atoms_1105_);
lean_dec(v___x_1104_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1121_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; lean_object* v___x_1115_; 
lean_inc(v_a_1100_);
v___x_1113_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v_evalsAtCache_1108_, v_originalExpr_1094_, v_a_1100_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 3, v___x_1113_);
v___x_1115_ = v___x_1111_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_atoms_1105_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_atomsAssignmentExprCache_1106_);
lean_ctor_set(v_reuseFailAlloc_1120_, 2, v_atomsAssignmentMapCache_1107_);
lean_ctor_set(v_reuseFailAlloc_1120_, 3, v___x_1113_);
lean_ctor_set(v_reuseFailAlloc_1120_, 4, v_theoryState_1109_);
v___x_1115_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
lean_object* v___x_1116_; lean_object* v___x_1118_; 
v___x_1116_ = lean_st_ref_put(v_a_1083_, v___x_1115_);
if (v_isShared_1103_ == 0)
{
v___x_1118_ = v___x_1102_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1100_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
else
{
lean_dec_ref(v_originalExpr_1094_);
return v___x_1099_;
}
}
else
{
lean_object* v_val_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
lean_dec_ref(v_evalsAtAtoms_x27_1095_);
lean_dec_ref(v_originalExpr_1094_);
v_val_1123_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1098_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_val_1123_);
lean_dec(v___x_1098_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
lean_ctor_set_tag(v___x_1125_, 0);
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_val_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_evalsAtAtoms___boxed(lean_object* v_reified_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_evalsAtAtoms(v_reified_1131_, v_a_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
lean_dec(v_a_1140_);
lean_dec_ref(v_a_1139_);
lean_dec(v_a_1138_);
lean_dec_ref(v_a_1137_);
lean_dec(v_a_1136_);
lean_dec_ref(v_a_1135_);
lean_dec(v_a_1134_);
lean_dec(v_a_1133_);
lean_dec_ref(v_a_1132_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(lean_object* v_reified_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v_originalExpr_1158_; lean_object* v_evalsAtAtoms_x27_1159_; lean_object* v___x_1160_; lean_object* v_evalsAtCache_1161_; lean_object* v___x_1162_; 
v_originalExpr_1158_ = lean_ctor_get(v_reified_1145_, 1);
lean_inc_ref(v_originalExpr_1158_);
v_evalsAtAtoms_x27_1159_ = lean_ctor_get(v_reified_1145_, 2);
lean_inc_ref(v_evalsAtAtoms_x27_1159_);
lean_dec_ref(v_reified_1145_);
v___x_1160_ = lean_st_ref_get(v_a_1147_);
v_evalsAtCache_1161_ = lean_ctor_get(v___x_1160_, 3);
lean_inc_ref(v_evalsAtCache_1161_);
lean_dec(v___x_1160_);
v___x_1162_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_evalsAtCache_1161_, v_originalExpr_1158_);
lean_dec_ref(v_evalsAtCache_1161_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v___x_1163_; 
lean_inc(v_a_1156_);
lean_inc_ref(v_a_1155_);
lean_inc(v_a_1154_);
lean_inc_ref(v_a_1153_);
lean_inc(v_a_1152_);
lean_inc_ref(v_a_1151_);
lean_inc(v_a_1150_);
lean_inc_ref(v_a_1149_);
lean_inc(v_a_1148_);
lean_inc(v_a_1147_);
lean_inc_ref(v_a_1146_);
v___x_1163_ = lean_apply_12(v_evalsAtAtoms_x27_1159_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, lean_box(0));
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1186_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1166_ = v___x_1163_;
v_isShared_1167_ = v_isSharedCheck_1186_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1163_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1186_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1168_; lean_object* v_atoms_1169_; lean_object* v_atomsAssignmentExprCache_1170_; lean_object* v_atomsAssignmentMapCache_1171_; lean_object* v_evalsAtCache_1172_; lean_object* v_theoryState_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1185_; 
v___x_1168_ = lean_st_ref_take(v_a_1147_);
v_atoms_1169_ = lean_ctor_get(v___x_1168_, 0);
v_atomsAssignmentExprCache_1170_ = lean_ctor_get(v___x_1168_, 1);
v_atomsAssignmentMapCache_1171_ = lean_ctor_get(v___x_1168_, 2);
v_evalsAtCache_1172_ = lean_ctor_get(v___x_1168_, 3);
v_theoryState_1173_ = lean_ctor_get(v___x_1168_, 4);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1175_ = v___x_1168_;
v_isShared_1176_ = v_isSharedCheck_1185_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_theoryState_1173_);
lean_inc(v_evalsAtCache_1172_);
lean_inc(v_atomsAssignmentMapCache_1171_);
lean_inc(v_atomsAssignmentExprCache_1170_);
lean_inc(v_atoms_1169_);
lean_dec(v___x_1168_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1185_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1177_; lean_object* v___x_1179_; 
lean_inc(v_a_1164_);
v___x_1177_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v_evalsAtCache_1172_, v_originalExpr_1158_, v_a_1164_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 3, v___x_1177_);
v___x_1179_ = v___x_1175_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_atoms_1169_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_atomsAssignmentExprCache_1170_);
lean_ctor_set(v_reuseFailAlloc_1184_, 2, v_atomsAssignmentMapCache_1171_);
lean_ctor_set(v_reuseFailAlloc_1184_, 3, v___x_1177_);
lean_ctor_set(v_reuseFailAlloc_1184_, 4, v_theoryState_1173_);
v___x_1179_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
lean_object* v___x_1180_; lean_object* v___x_1182_; 
v___x_1180_ = lean_st_ref_put(v_a_1147_, v___x_1179_);
if (v_isShared_1167_ == 0)
{
v___x_1182_ = v___x_1166_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1164_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
}
else
{
lean_dec_ref(v_originalExpr_1158_);
return v___x_1163_;
}
}
else
{
lean_object* v_val_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
lean_dec_ref(v_evalsAtAtoms_x27_1159_);
lean_dec_ref(v_originalExpr_1158_);
v_val_1187_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1162_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_val_1187_);
lean_dec(v___x_1162_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
lean_ctor_set_tag(v___x_1189_, 0);
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_val_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms___boxed(lean_object* v_reified_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(v_reified_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_);
lean_dec(v_a_1206_);
lean_dec_ref(v_a_1205_);
lean_dec(v_a_1204_);
lean_dec_ref(v_a_1203_);
lean_dec(v_a_1202_);
lean_dec_ref(v_a_1201_);
lean_dec(v_a_1200_);
lean_dec_ref(v_a_1199_);
lean_dec(v_a_1198_);
lean_dec(v_a_1197_);
lean_dec_ref(v_a_1196_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_run_spec__0___redArg(size_t v_sz_1209_, size_t v_i_1210_, lean_object* v_bs_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
uint8_t v___x_1219_; 
v___x_1219_ = lean_usize_dec_lt(v_i_1210_, v_sz_1209_);
if (v___x_1219_ == 0)
{
lean_object* v___x_1220_; 
v___x_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1220_, 0, v_bs_1211_);
return v___x_1220_;
}
else
{
lean_object* v_v_1221_; lean_object* v_name_1222_; lean_object* v_type_1223_; lean_object* v_value_1224_; lean_object* v_source_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1248_; 
v_v_1221_ = lean_array_uget(v_bs_1211_, v_i_1210_);
v_name_1222_ = lean_ctor_get(v_v_1221_, 0);
v_type_1223_ = lean_ctor_get(v_v_1221_, 1);
v_value_1224_ = lean_ctor_get(v_v_1221_, 2);
v_source_1225_ = lean_ctor_get(v_v_1221_, 3);
v_isSharedCheck_1248_ = !lean_is_exclusive(v_v_1221_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1227_ = v_v_1221_;
v_isShared_1228_ = v_isSharedCheck_1248_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_source_1225_);
lean_inc(v_value_1224_);
lean_inc(v_type_1223_);
lean_inc(v_name_1222_);
lean_dec(v_v_1221_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1248_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1229_; lean_object* v_bs_x27_1230_; lean_object* v___x_1231_; 
v___x_1229_ = lean_unsigned_to_nat(0u);
v_bs_x27_1230_ = lean_array_uset(v_bs_1211_, v_i_1210_, v___x_1229_);
v___x_1231_ = l_Lean_Meta_Sym_shareCommon(v_type_1223_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; lean_object* v___x_1234_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_a_1232_);
lean_dec_ref_known(v___x_1231_, 1);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 1, v_a_1232_);
v___x_1234_ = v___x_1227_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_name_1222_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_a_1232_);
lean_ctor_set(v_reuseFailAlloc_1239_, 2, v_value_1224_);
lean_ctor_set(v_reuseFailAlloc_1239_, 3, v_source_1225_);
v___x_1234_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
size_t v___x_1235_; size_t v___x_1236_; lean_object* v___x_1237_; 
v___x_1235_ = ((size_t)1ULL);
v___x_1236_ = lean_usize_add(v_i_1210_, v___x_1235_);
v___x_1237_ = lean_array_uset(v_bs_x27_1230_, v_i_1210_, v___x_1234_);
v_i_1210_ = v___x_1236_;
v_bs_1211_ = v___x_1237_;
goto _start;
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec_ref(v_bs_x27_1230_);
lean_del_object(v___x_1227_);
lean_dec(v_source_1225_);
lean_dec_ref(v_value_1224_);
lean_dec(v_name_1222_);
v_a_1240_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1231_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1231_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_run_spec__0___redArg___boxed(lean_object* v_sz_1249_, lean_object* v_i_1250_, lean_object* v_bs_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
size_t v_sz_boxed_1259_; size_t v_i_boxed_1260_; lean_object* v_res_1261_; 
v_sz_boxed_1259_ = lean_unbox_usize(v_sz_1249_);
lean_dec(v_sz_1249_);
v_i_boxed_1260_ = lean_unbox_usize(v_i_1250_);
lean_dec(v_i_1250_);
v_res_1261_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_run_spec__0___redArg(v_sz_boxed_1259_, v_i_boxed_1260_, v_bs_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
return v_res_1261_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1262_ = lean_box(0);
v___x_1263_ = lean_unsigned_to_nat(16u);
v___x_1264_ = lean_mk_array(v___x_1263_, v___x_1262_);
return v___x_1264_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1265_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__0);
v___x_1266_ = lean_unsigned_to_nat(0u);
v___x_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
lean_ctor_set(v___x_1267_, 1, v___x_1265_);
return v___x_1267_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__4(void){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1272_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__3));
v___x_1273_ = lean_box(0);
v___x_1274_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__1);
v___x_1275_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1274_);
lean_ctor_set(v___x_1275_, 1, v___x_1273_);
lean_ctor_set(v___x_1275_, 2, v___x_1273_);
lean_ctor_set(v___x_1275_, 3, v___x_1274_);
lean_ctor_set(v___x_1275_, 4, v___x_1272_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg(lean_object* v_m_1276_, lean_object* v_hypotheses_1277_, lean_object* v_cfg_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_){
_start:
{
size_t v_sz_1289_; size_t v___x_1290_; lean_object* v___x_1291_; 
v_sz_1289_ = lean_array_size(v_hypotheses_1277_);
v___x_1290_ = ((size_t)0ULL);
v___x_1291_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_run_spec__0___redArg(v_sz_1289_, v___x_1290_, v_hypotheses_1277_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v_a_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v_a_1292_ = lean_ctor_get(v___x_1291_, 0);
lean_inc(v_a_1292_);
lean_dec_ref_known(v___x_1291_, 1);
v___x_1293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1293_, 0, v_a_1292_);
lean_ctor_set(v___x_1293_, 1, v_cfg_1278_);
v___x_1294_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__4, &l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__4);
v___x_1295_ = lean_st_mk_ref(v___x_1294_);
lean_inc(v_a_1287_);
lean_inc_ref(v_a_1286_);
lean_inc(v_a_1285_);
lean_inc_ref(v_a_1284_);
lean_inc(v_a_1283_);
lean_inc_ref(v_a_1282_);
lean_inc(v_a_1281_);
lean_inc_ref(v_a_1280_);
lean_inc(v_a_1279_);
lean_inc(v___x_1295_);
v___x_1296_ = lean_apply_12(v_m_1276_, v___x_1293_, v___x_1295_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, lean_box(0));
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1305_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1299_ = v___x_1296_;
v_isShared_1300_ = v_isSharedCheck_1305_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1296_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1305_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1301_; lean_object* v___x_1303_; 
v___x_1301_ = lean_st_ref_get(v___x_1295_);
lean_dec(v___x_1295_);
lean_dec(v___x_1301_);
if (v_isShared_1300_ == 0)
{
v___x_1303_ = v___x_1299_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1297_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
else
{
lean_dec(v___x_1295_);
return v___x_1296_;
}
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_dec_ref(v_cfg_1278_);
lean_dec_ref(v_m_1276_);
v_a_1306_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1291_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1291_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___boxed(lean_object* v_m_1314_, lean_object* v_hypotheses_1315_, lean_object* v_cfg_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg(v_m_1314_, v_hypotheses_1315_, v_cfg_1316_, v_a_1317_, v_a_1318_, v_a_1319_, v_a_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_, v_a_1325_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
lean_dec(v_a_1323_);
lean_dec_ref(v_a_1322_);
lean_dec(v_a_1321_);
lean_dec_ref(v_a_1320_);
lean_dec(v_a_1319_);
lean_dec_ref(v_a_1318_);
lean_dec(v_a_1317_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_run(lean_object* v_00_u03b1_1328_, lean_object* v_m_1329_, lean_object* v_hypotheses_1330_, lean_object* v_cfg_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg(v_m_1329_, v_hypotheses_1330_, v_cfg_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_run___boxed(lean_object* v_00_u03b1_1343_, lean_object* v_m_1344_, lean_object* v_hypotheses_1345_, lean_object* v_cfg_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_run(v_00_u03b1_1343_, v_m_1344_, v_hypotheses_1345_, v_cfg_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
lean_dec(v_a_1355_);
lean_dec_ref(v_a_1354_);
lean_dec(v_a_1353_);
lean_dec_ref(v_a_1352_);
lean_dec(v_a_1351_);
lean_dec_ref(v_a_1350_);
lean_dec(v_a_1349_);
lean_dec_ref(v_a_1348_);
lean_dec(v_a_1347_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_run_spec__0(size_t v_sz_1358_, size_t v_i_1359_, lean_object* v_bs_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v___x_1371_; 
v___x_1371_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_run_spec__0___redArg(v_sz_1358_, v_i_1359_, v_bs_1360_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_run_spec__0___boxed(lean_object* v_sz_1372_, lean_object* v_i_1373_, lean_object* v_bs_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
size_t v_sz_boxed_1385_; size_t v_i_boxed_1386_; lean_object* v_res_1387_; 
v_sz_boxed_1385_ = lean_unbox_usize(v_sz_1372_);
lean_dec(v_sz_1372_);
v_i_boxed_1386_ = lean_unbox_usize(v_i_1373_);
lean_dec(v_i_1373_);
v_res_1387_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_run_spec__0(v_sz_boxed_1385_, v_i_boxed_1386_, v_bs_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__2(lean_object* v_x_1388_, lean_object* v_x_1389_){
_start:
{
if (lean_obj_tag(v_x_1389_) == 0)
{
return v_x_1388_;
}
else
{
lean_object* v_key_1390_; lean_object* v_value_1391_; lean_object* v_tail_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v_key_1390_ = lean_ctor_get(v_x_1389_, 0);
v_value_1391_ = lean_ctor_get(v_x_1389_, 1);
v_tail_1392_ = lean_ctor_get(v_x_1389_, 2);
lean_inc(v_value_1391_);
lean_inc(v_key_1390_);
v___x_1393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1393_, 0, v_key_1390_);
lean_ctor_set(v___x_1393_, 1, v_value_1391_);
v___x_1394_ = lean_array_push(v_x_1388_, v___x_1393_);
v_x_1388_ = v___x_1394_;
v_x_1389_ = v_tail_1392_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__2___boxed(lean_object* v_x_1396_, lean_object* v_x_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__2(v_x_1396_, v_x_1397_);
lean_dec(v_x_1397_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__3(lean_object* v_as_1399_, size_t v_i_1400_, size_t v_stop_1401_, lean_object* v_b_1402_){
_start:
{
uint8_t v___x_1403_; 
v___x_1403_ = lean_usize_dec_eq(v_i_1400_, v_stop_1401_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; lean_object* v___x_1405_; size_t v___x_1406_; size_t v___x_1407_; 
v___x_1404_ = lean_array_uget_borrowed(v_as_1399_, v_i_1400_);
v___x_1405_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__2(v_b_1402_, v___x_1404_);
v___x_1406_ = ((size_t)1ULL);
v___x_1407_ = lean_usize_add(v_i_1400_, v___x_1406_);
v_i_1400_ = v___x_1407_;
v_b_1402_ = v___x_1405_;
goto _start;
}
else
{
return v_b_1402_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__3___boxed(lean_object* v_as_1409_, lean_object* v_i_1410_, lean_object* v_stop_1411_, lean_object* v_b_1412_){
_start:
{
size_t v_i_boxed_1413_; size_t v_stop_boxed_1414_; lean_object* v_res_1415_; 
v_i_boxed_1413_ = lean_unbox_usize(v_i_1410_);
lean_dec(v_i_1410_);
v_stop_boxed_1414_ = lean_unbox_usize(v_stop_1411_);
lean_dec(v_stop_1411_);
v_res_1415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__3(v_as_1409_, v_i_boxed_1413_, v_stop_boxed_1414_, v_b_1412_);
lean_dec_ref(v_as_1409_);
return v_res_1415_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___redArg___lam__0(lean_object* v_x1_1416_, lean_object* v_x2_1417_){
_start:
{
lean_object* v_snd_1418_; lean_object* v_snd_1419_; lean_object* v_atomNumber_1420_; lean_object* v_atomNumber_1421_; uint8_t v___x_1422_; 
v_snd_1418_ = lean_ctor_get(v_x1_1416_, 1);
v_snd_1419_ = lean_ctor_get(v_x2_1417_, 1);
v_atomNumber_1420_ = lean_ctor_get(v_snd_1418_, 1);
v_atomNumber_1421_ = lean_ctor_get(v_snd_1419_, 1);
v___x_1422_ = lean_nat_dec_lt(v_atomNumber_1420_, v_atomNumber_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___redArg___lam__0___boxed(lean_object* v_x1_1423_, lean_object* v_x2_1424_){
_start:
{
uint8_t v_res_1425_; lean_object* v_r_1426_; 
v_res_1425_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___redArg___lam__0(v_x1_1423_, v_x2_1424_);
lean_dec_ref(v_x2_1424_);
lean_dec_ref(v_x1_1423_);
v_r_1426_ = lean_box(v_res_1425_);
return v_r_1426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1_spec__1___redArg(lean_object* v_hi_1427_, lean_object* v_pivot_1428_, lean_object* v_as_1429_, lean_object* v_i_1430_, lean_object* v_k_1431_){
_start:
{
uint8_t v___x_1432_; 
v___x_1432_ = lean_nat_dec_lt(v_k_1431_, v_hi_1427_);
if (v___x_1432_ == 0)
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
lean_dec(v_k_1431_);
v___x_1433_ = lean_array_fswap(v_as_1429_, v_i_1430_, v_hi_1427_);
v___x_1434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1434_, 0, v_i_1430_);
lean_ctor_set(v___x_1434_, 1, v___x_1433_);
return v___x_1434_;
}
else
{
lean_object* v___x_1435_; lean_object* v_snd_1436_; lean_object* v_snd_1437_; lean_object* v_atomNumber_1438_; lean_object* v_atomNumber_1439_; uint8_t v___x_1440_; 
v___x_1435_ = lean_array_fget_borrowed(v_as_1429_, v_k_1431_);
v_snd_1436_ = lean_ctor_get(v___x_1435_, 1);
v_snd_1437_ = lean_ctor_get(v_pivot_1428_, 1);
v_atomNumber_1438_ = lean_ctor_get(v_snd_1436_, 1);
v_atomNumber_1439_ = lean_ctor_get(v_snd_1437_, 1);
v___x_1440_ = lean_nat_dec_lt(v_atomNumber_1438_, v_atomNumber_1439_);
if (v___x_1440_ == 0)
{
lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1441_ = lean_unsigned_to_nat(1u);
v___x_1442_ = lean_nat_add(v_k_1431_, v___x_1441_);
lean_dec(v_k_1431_);
v_k_1431_ = v___x_1442_;
goto _start;
}
else
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1444_ = lean_array_fswap(v_as_1429_, v_i_1430_, v_k_1431_);
v___x_1445_ = lean_unsigned_to_nat(1u);
v___x_1446_ = lean_nat_add(v_i_1430_, v___x_1445_);
lean_dec(v_i_1430_);
v___x_1447_ = lean_nat_add(v_k_1431_, v___x_1445_);
lean_dec(v_k_1431_);
v_as_1429_ = v___x_1444_;
v_i_1430_ = v___x_1446_;
v_k_1431_ = v___x_1447_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1_spec__1___redArg___boxed(lean_object* v_hi_1449_, lean_object* v_pivot_1450_, lean_object* v_as_1451_, lean_object* v_i_1452_, lean_object* v_k_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1_spec__1___redArg(v_hi_1449_, v_pivot_1450_, v_as_1451_, v_i_1452_, v_k_1453_);
lean_dec_ref(v_pivot_1450_);
lean_dec(v_hi_1449_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___redArg(lean_object* v_n_1455_, lean_object* v_as_1456_, lean_object* v_lo_1457_, lean_object* v_hi_1458_){
_start:
{
lean_object* v___y_1460_; uint8_t v___x_1470_; 
v___x_1470_ = lean_nat_dec_lt(v_lo_1457_, v_hi_1458_);
if (v___x_1470_ == 0)
{
lean_dec(v_lo_1457_);
return v_as_1456_;
}
else
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v_mid_1473_; lean_object* v___y_1475_; lean_object* v___y_1481_; lean_object* v___x_1486_; lean_object* v___x_1487_; uint8_t v___x_1488_; 
v___x_1471_ = lean_nat_add(v_lo_1457_, v_hi_1458_);
v___x_1472_ = lean_unsigned_to_nat(1u);
v_mid_1473_ = lean_nat_shiftr(v___x_1471_, v___x_1472_);
lean_dec(v___x_1471_);
v___x_1486_ = lean_array_fget_borrowed(v_as_1456_, v_mid_1473_);
v___x_1487_ = lean_array_fget_borrowed(v_as_1456_, v_lo_1457_);
v___x_1488_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___redArg___lam__0(v___x_1486_, v___x_1487_);
if (v___x_1488_ == 0)
{
v___y_1481_ = v_as_1456_;
goto v___jp_1480_;
}
else
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_array_fswap(v_as_1456_, v_lo_1457_, v_mid_1473_);
v___y_1481_ = v___x_1489_;
goto v___jp_1480_;
}
v___jp_1474_:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; uint8_t v___x_1478_; 
v___x_1476_ = lean_array_fget_borrowed(v___y_1475_, v_mid_1473_);
v___x_1477_ = lean_array_fget_borrowed(v___y_1475_, v_hi_1458_);
v___x_1478_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___redArg___lam__0(v___x_1476_, v___x_1477_);
if (v___x_1478_ == 0)
{
lean_dec(v_mid_1473_);
v___y_1460_ = v___y_1475_;
goto v___jp_1459_;
}
else
{
lean_object* v___x_1479_; 
v___x_1479_ = lean_array_fswap(v___y_1475_, v_mid_1473_, v_hi_1458_);
lean_dec(v_mid_1473_);
v___y_1460_ = v___x_1479_;
goto v___jp_1459_;
}
}
v___jp_1480_:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; uint8_t v___x_1484_; 
v___x_1482_ = lean_array_fget_borrowed(v___y_1481_, v_hi_1458_);
v___x_1483_ = lean_array_fget_borrowed(v___y_1481_, v_lo_1457_);
v___x_1484_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___redArg___lam__0(v___x_1482_, v___x_1483_);
if (v___x_1484_ == 0)
{
v___y_1475_ = v___y_1481_;
goto v___jp_1474_;
}
else
{
lean_object* v___x_1485_; 
v___x_1485_ = lean_array_fswap(v___y_1481_, v_lo_1457_, v_hi_1458_);
v___y_1475_ = v___x_1485_;
goto v___jp_1474_;
}
}
}
v___jp_1459_:
{
lean_object* v_pivot_1461_; lean_object* v___x_1462_; lean_object* v_fst_1463_; lean_object* v_snd_1464_; uint8_t v___x_1465_; 
v_pivot_1461_ = lean_array_fget(v___y_1460_, v_hi_1458_);
lean_inc_n(v_lo_1457_, 2);
v___x_1462_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1_spec__1___redArg(v_hi_1458_, v_pivot_1461_, v___y_1460_, v_lo_1457_, v_lo_1457_);
lean_dec(v_pivot_1461_);
v_fst_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_fst_1463_);
v_snd_1464_ = lean_ctor_get(v___x_1462_, 1);
lean_inc(v_snd_1464_);
lean_dec_ref(v___x_1462_);
v___x_1465_ = lean_nat_dec_le(v_hi_1458_, v_fst_1463_);
if (v___x_1465_ == 0)
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1466_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___redArg(v_n_1455_, v_snd_1464_, v_lo_1457_, v_fst_1463_);
v___x_1467_ = lean_unsigned_to_nat(1u);
v___x_1468_ = lean_nat_add(v_fst_1463_, v___x_1467_);
lean_dec(v_fst_1463_);
v_as_1456_ = v___x_1466_;
v_lo_1457_ = v___x_1468_;
goto _start;
}
else
{
lean_dec(v_fst_1463_);
lean_dec(v_lo_1457_);
return v_snd_1464_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___redArg___boxed(lean_object* v_n_1490_, lean_object* v_as_1491_, lean_object* v_lo_1492_, lean_object* v_hi_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___redArg(v_n_1490_, v_as_1491_, v_lo_1492_, v_hi_1493_);
lean_dec(v_hi_1493_);
lean_dec(v_n_1490_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__0(size_t v_sz_1495_, size_t v_i_1496_, lean_object* v_bs_1497_){
_start:
{
uint8_t v___x_1498_; 
v___x_1498_ = lean_usize_dec_lt(v_i_1496_, v_sz_1495_);
if (v___x_1498_ == 0)
{
return v_bs_1497_;
}
else
{
lean_object* v_v_1499_; lean_object* v_snd_1500_; lean_object* v_fst_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1515_; 
v_v_1499_ = lean_array_uget(v_bs_1497_, v_i_1496_);
v_snd_1500_ = lean_ctor_get(v_v_1499_, 1);
v_fst_1501_ = lean_ctor_get(v_v_1499_, 0);
v_isSharedCheck_1515_ = !lean_is_exclusive(v_v_1499_);
if (v_isSharedCheck_1515_ == 0)
{
v___x_1503_ = v_v_1499_;
v_isShared_1504_ = v_isSharedCheck_1515_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_snd_1500_);
lean_inc(v_fst_1501_);
lean_dec(v_v_1499_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1515_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v_width_1505_; lean_object* v___x_1506_; lean_object* v_bs_x27_1507_; lean_object* v___x_1509_; 
v_width_1505_ = lean_ctor_get(v_snd_1500_, 0);
lean_inc(v_width_1505_);
lean_dec(v_snd_1500_);
v___x_1506_ = lean_unsigned_to_nat(0u);
v_bs_x27_1507_ = lean_array_uset(v_bs_1497_, v_i_1496_, v___x_1506_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 1, v_fst_1501_);
lean_ctor_set(v___x_1503_, 0, v_width_1505_);
v___x_1509_ = v___x_1503_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_width_1505_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_fst_1501_);
v___x_1509_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
size_t v___x_1510_; size_t v___x_1511_; lean_object* v___x_1512_; 
v___x_1510_ = ((size_t)1ULL);
v___x_1511_ = lean_usize_add(v_i_1496_, v___x_1510_);
v___x_1512_ = lean_array_uset(v_bs_x27_1507_, v_i_1496_, v___x_1509_);
v_i_1496_ = v___x_1511_;
v_bs_1497_ = v___x_1512_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__0___boxed(lean_object* v_sz_1516_, lean_object* v_i_1517_, lean_object* v_bs_1518_){
_start:
{
size_t v_sz_boxed_1519_; size_t v_i_boxed_1520_; lean_object* v_res_1521_; 
v_sz_boxed_1519_ = lean_unbox_usize(v_sz_1516_);
lean_dec(v_sz_1516_);
v_i_boxed_1520_ = lean_unbox_usize(v_i_1517_);
lean_dec(v_i_1517_);
v_res_1521_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__0(v_sz_boxed_1519_, v_i_boxed_1520_, v_bs_1518_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atoms___redArg(lean_object* v_a_1522_){
_start:
{
lean_object* v___x_1524_; lean_object* v___y_1526_; lean_object* v___y_1532_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1538_; lean_object* v___y_1539_; lean_object* v___y_1540_; lean_object* v___y_1541_; lean_object* v___y_1544_; lean_object* v_atoms_1551_; lean_object* v_size_1552_; lean_object* v_buckets_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
v___x_1524_ = lean_st_ref_get(v_a_1522_);
v_atoms_1551_ = lean_ctor_get(v___x_1524_, 0);
lean_inc_ref(v_atoms_1551_);
lean_dec(v___x_1524_);
v_size_1552_ = lean_ctor_get(v_atoms_1551_, 0);
lean_inc(v_size_1552_);
v_buckets_1553_ = lean_ctor_get(v_atoms_1551_, 1);
lean_inc_ref(v_buckets_1553_);
lean_dec_ref(v_atoms_1551_);
v___x_1554_ = lean_mk_empty_array_with_capacity(v_size_1552_);
lean_dec(v_size_1552_);
v___x_1555_ = lean_unsigned_to_nat(0u);
v___x_1556_ = lean_array_get_size(v_buckets_1553_);
v___x_1557_ = lean_nat_dec_lt(v___x_1555_, v___x_1556_);
if (v___x_1557_ == 0)
{
lean_dec_ref(v_buckets_1553_);
v___y_1544_ = v___x_1554_;
goto v___jp_1543_;
}
else
{
size_t v___x_1558_; size_t v___x_1559_; lean_object* v___x_1560_; 
v___x_1558_ = ((size_t)0ULL);
v___x_1559_ = lean_usize_of_nat(v___x_1556_);
v___x_1560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__3(v_buckets_1553_, v___x_1558_, v___x_1559_, v___x_1554_);
lean_dec_ref(v_buckets_1553_);
v___y_1544_ = v___x_1560_;
goto v___jp_1543_;
}
v___jp_1525_:
{
size_t v_sz_1527_; size_t v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v_sz_1527_ = lean_array_size(v___y_1526_);
v___x_1528_ = ((size_t)0ULL);
v___x_1529_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__0(v_sz_1527_, v___x_1528_, v___y_1526_);
v___x_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
return v___x_1530_;
}
v___jp_1531_:
{
lean_object* v___x_1536_; 
v___x_1536_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___redArg(v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
lean_dec(v___y_1535_);
lean_dec(v___y_1532_);
v___y_1526_ = v___x_1536_;
goto v___jp_1525_;
}
v___jp_1537_:
{
uint8_t v___x_1542_; 
v___x_1542_ = lean_nat_dec_le(v___y_1541_, v___y_1540_);
if (v___x_1542_ == 0)
{
lean_dec(v___y_1540_);
lean_inc(v___y_1541_);
v___y_1532_ = v___y_1538_;
v___y_1533_ = v___y_1539_;
v___y_1534_ = v___y_1541_;
v___y_1535_ = v___y_1541_;
goto v___jp_1531_;
}
else
{
v___y_1532_ = v___y_1538_;
v___y_1533_ = v___y_1539_;
v___y_1534_ = v___y_1541_;
v___y_1535_ = v___y_1540_;
goto v___jp_1531_;
}
}
v___jp_1543_:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; uint8_t v___x_1547_; 
v___x_1545_ = lean_array_get_size(v___y_1544_);
v___x_1546_ = lean_unsigned_to_nat(0u);
v___x_1547_ = lean_nat_dec_eq(v___x_1545_, v___x_1546_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; 
v___x_1548_ = lean_unsigned_to_nat(1u);
v___x_1549_ = lean_nat_sub(v___x_1545_, v___x_1548_);
v___x_1550_ = lean_nat_dec_le(v___x_1546_, v___x_1549_);
if (v___x_1550_ == 0)
{
lean_inc(v___x_1549_);
v___y_1538_ = v___x_1545_;
v___y_1539_ = v___y_1544_;
v___y_1540_ = v___x_1549_;
v___y_1541_ = v___x_1549_;
goto v___jp_1537_;
}
else
{
v___y_1538_ = v___x_1545_;
v___y_1539_ = v___y_1544_;
v___y_1540_ = v___x_1549_;
v___y_1541_ = v___x_1546_;
goto v___jp_1537_;
}
}
else
{
v___y_1526_ = v___y_1544_;
goto v___jp_1525_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atoms___redArg___boxed(lean_object* v_a_1561_, lean_object* v_a_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atoms___redArg(v_a_1561_);
lean_dec(v_a_1561_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atoms(lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_){
_start:
{
lean_object* v___x_1576_; 
v___x_1576_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atoms___redArg(v_a_1565_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atoms___boxed(lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atoms(v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
lean_dec(v_a_1587_);
lean_dec_ref(v_a_1586_);
lean_dec(v_a_1585_);
lean_dec_ref(v_a_1584_);
lean_dec(v_a_1583_);
lean_dec_ref(v_a_1582_);
lean_dec(v_a_1581_);
lean_dec_ref(v_a_1580_);
lean_dec(v_a_1579_);
lean_dec(v_a_1578_);
lean_dec_ref(v_a_1577_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1(lean_object* v_n_1590_, lean_object* v_as_1591_, lean_object* v_lo_1592_, lean_object* v_hi_1593_, lean_object* v_w_1594_, lean_object* v_hlo_1595_, lean_object* v_hhi_1596_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___redArg(v_n_1590_, v_as_1591_, v_lo_1592_, v_hi_1593_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___boxed(lean_object* v_n_1598_, lean_object* v_as_1599_, lean_object* v_lo_1600_, lean_object* v_hi_1601_, lean_object* v_w_1602_, lean_object* v_hlo_1603_, lean_object* v_hhi_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1(v_n_1598_, v_as_1599_, v_lo_1600_, v_hi_1601_, v_w_1602_, v_hlo_1603_, v_hhi_1604_);
lean_dec(v_hi_1601_);
lean_dec(v_n_1598_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1_spec__1(lean_object* v_n_1606_, lean_object* v_lo_1607_, lean_object* v_hi_1608_, lean_object* v_hhi_1609_, lean_object* v_pivot_1610_, lean_object* v_as_1611_, lean_object* v_i_1612_, lean_object* v_k_1613_, lean_object* v_ilo_1614_, lean_object* v_ik_1615_, lean_object* v_w_1616_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1_spec__1___redArg(v_hi_1608_, v_pivot_1610_, v_as_1611_, v_i_1612_, v_k_1613_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1_spec__1___boxed(lean_object* v_n_1618_, lean_object* v_lo_1619_, lean_object* v_hi_1620_, lean_object* v_hhi_1621_, lean_object* v_pivot_1622_, lean_object* v_as_1623_, lean_object* v_i_1624_, lean_object* v_k_1625_, lean_object* v_ilo_1626_, lean_object* v_ik_1627_, lean_object* v_w_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1_spec__1(v_n_1618_, v_lo_1619_, v_hi_1620_, v_hhi_1621_, v_pivot_1622_, v_as_1623_, v_i_1624_, v_k_1625_, v_ilo_1626_, v_ik_1627_, v_w_1628_);
lean_dec_ref(v_pivot_1622_);
lean_dec(v_hi_1620_);
lean_dec(v_lo_1619_);
lean_dec(v_n_1618_);
return v_res_1629_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__2___redArg(lean_object* v_a_1630_, lean_object* v_x_1631_){
_start:
{
if (lean_obj_tag(v_x_1631_) == 0)
{
uint8_t v___x_1632_; 
v___x_1632_ = 0;
return v___x_1632_;
}
else
{
lean_object* v_key_1633_; lean_object* v_tail_1634_; uint8_t v___x_1635_; 
v_key_1633_ = lean_ctor_get(v_x_1631_, 0);
v_tail_1634_ = lean_ctor_get(v_x_1631_, 2);
v___x_1635_ = lean_nat_dec_eq(v_key_1633_, v_a_1630_);
if (v___x_1635_ == 0)
{
v_x_1631_ = v_tail_1634_;
goto _start;
}
else
{
return v___x_1635_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_a_1637_, lean_object* v_x_1638_){
_start:
{
uint8_t v_res_1639_; lean_object* v_r_1640_; 
v_res_1639_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__2___redArg(v_a_1637_, v_x_1638_);
lean_dec(v_x_1638_);
lean_dec(v_a_1637_);
v_r_1640_ = lean_box(v_res_1639_);
return v_r_1640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__4___redArg(lean_object* v_a_1641_, lean_object* v_b_1642_, lean_object* v_x_1643_){
_start:
{
if (lean_obj_tag(v_x_1643_) == 0)
{
lean_dec(v_b_1642_);
lean_dec(v_a_1641_);
return v_x_1643_;
}
else
{
lean_object* v_key_1644_; lean_object* v_value_1645_; lean_object* v_tail_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1658_; 
v_key_1644_ = lean_ctor_get(v_x_1643_, 0);
v_value_1645_ = lean_ctor_get(v_x_1643_, 1);
v_tail_1646_ = lean_ctor_get(v_x_1643_, 2);
v_isSharedCheck_1658_ = !lean_is_exclusive(v_x_1643_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1648_ = v_x_1643_;
v_isShared_1649_ = v_isSharedCheck_1658_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_tail_1646_);
lean_inc(v_value_1645_);
lean_inc(v_key_1644_);
lean_dec(v_x_1643_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1658_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
uint8_t v___x_1650_; 
v___x_1650_ = lean_nat_dec_eq(v_key_1644_, v_a_1641_);
if (v___x_1650_ == 0)
{
lean_object* v___x_1651_; lean_object* v___x_1653_; 
v___x_1651_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__4___redArg(v_a_1641_, v_b_1642_, v_tail_1646_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 2, v___x_1651_);
v___x_1653_ = v___x_1648_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_key_1644_);
lean_ctor_set(v_reuseFailAlloc_1654_, 1, v_value_1645_);
lean_ctor_set(v_reuseFailAlloc_1654_, 2, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
else
{
lean_object* v___x_1656_; 
lean_dec(v_value_1645_);
lean_dec(v_key_1644_);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 1, v_b_1642_);
lean_ctor_set(v___x_1648_, 0, v_a_1641_);
v___x_1656_ = v___x_1648_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1641_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_b_1642_);
lean_ctor_set(v_reuseFailAlloc_1657_, 2, v_tail_1646_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__3_spec__6_spec__8___redArg(lean_object* v_x_1659_, lean_object* v_x_1660_){
_start:
{
if (lean_obj_tag(v_x_1660_) == 0)
{
return v_x_1659_;
}
else
{
lean_object* v_key_1661_; lean_object* v_value_1662_; lean_object* v_tail_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1686_; 
v_key_1661_ = lean_ctor_get(v_x_1660_, 0);
v_value_1662_ = lean_ctor_get(v_x_1660_, 1);
v_tail_1663_ = lean_ctor_get(v_x_1660_, 2);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_x_1660_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1665_ = v_x_1660_;
v_isShared_1666_ = v_isSharedCheck_1686_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_tail_1663_);
lean_inc(v_value_1662_);
lean_inc(v_key_1661_);
lean_dec(v_x_1660_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1686_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1667_; uint64_t v___x_1668_; uint64_t v___x_1669_; uint64_t v___x_1670_; uint64_t v_fold_1671_; uint64_t v___x_1672_; uint64_t v___x_1673_; uint64_t v___x_1674_; size_t v___x_1675_; size_t v___x_1676_; size_t v___x_1677_; size_t v___x_1678_; size_t v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1682_; 
v___x_1667_ = lean_array_get_size(v_x_1659_);
v___x_1668_ = lean_uint64_of_nat(v_key_1661_);
v___x_1669_ = 32ULL;
v___x_1670_ = lean_uint64_shift_right(v___x_1668_, v___x_1669_);
v_fold_1671_ = lean_uint64_xor(v___x_1668_, v___x_1670_);
v___x_1672_ = 16ULL;
v___x_1673_ = lean_uint64_shift_right(v_fold_1671_, v___x_1672_);
v___x_1674_ = lean_uint64_xor(v_fold_1671_, v___x_1673_);
v___x_1675_ = lean_uint64_to_usize(v___x_1674_);
v___x_1676_ = lean_usize_of_nat(v___x_1667_);
v___x_1677_ = ((size_t)1ULL);
v___x_1678_ = lean_usize_sub(v___x_1676_, v___x_1677_);
v___x_1679_ = lean_usize_land(v___x_1675_, v___x_1678_);
v___x_1680_ = lean_array_uget_borrowed(v_x_1659_, v___x_1679_);
lean_inc(v___x_1680_);
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 2, v___x_1680_);
v___x_1682_ = v___x_1665_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_key_1661_);
lean_ctor_set(v_reuseFailAlloc_1685_, 1, v_value_1662_);
lean_ctor_set(v_reuseFailAlloc_1685_, 2, v___x_1680_);
v___x_1682_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
lean_object* v___x_1683_; 
v___x_1683_ = lean_array_uset(v_x_1659_, v___x_1679_, v___x_1682_);
v_x_1659_ = v___x_1683_;
v_x_1660_ = v_tail_1663_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__3_spec__6___redArg(lean_object* v_i_1687_, lean_object* v_source_1688_, lean_object* v_target_1689_){
_start:
{
lean_object* v___x_1690_; uint8_t v___x_1691_; 
v___x_1690_ = lean_array_get_size(v_source_1688_);
v___x_1691_ = lean_nat_dec_lt(v_i_1687_, v___x_1690_);
if (v___x_1691_ == 0)
{
lean_dec_ref(v_source_1688_);
lean_dec(v_i_1687_);
return v_target_1689_;
}
else
{
lean_object* v_es_1692_; lean_object* v___x_1693_; lean_object* v_source_1694_; lean_object* v_target_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v_es_1692_ = lean_array_fget(v_source_1688_, v_i_1687_);
v___x_1693_ = lean_box(0);
v_source_1694_ = lean_array_fset(v_source_1688_, v_i_1687_, v___x_1693_);
v_target_1695_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__3_spec__6_spec__8___redArg(v_target_1689_, v_es_1692_);
v___x_1696_ = lean_unsigned_to_nat(1u);
v___x_1697_ = lean_nat_add(v_i_1687_, v___x_1696_);
lean_dec(v_i_1687_);
v_i_1687_ = v___x_1697_;
v_source_1688_ = v_source_1694_;
v_target_1689_ = v_target_1695_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__3___redArg(lean_object* v_data_1699_){
_start:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v_nbuckets_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1700_ = lean_array_get_size(v_data_1699_);
v___x_1701_ = lean_unsigned_to_nat(2u);
v_nbuckets_1702_ = lean_nat_mul(v___x_1700_, v___x_1701_);
v___x_1703_ = lean_unsigned_to_nat(0u);
v___x_1704_ = lean_box(0);
v___x_1705_ = lean_mk_array(v_nbuckets_1702_, v___x_1704_);
v___x_1706_ = lean_array_propagate_mark(v_data_1699_, v___x_1705_);
v___x_1707_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__3_spec__6___redArg(v___x_1703_, v_data_1699_, v___x_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1___redArg(lean_object* v_m_1708_, lean_object* v_a_1709_, lean_object* v_b_1710_){
_start:
{
lean_object* v_size_1711_; lean_object* v_buckets_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1755_; 
v_size_1711_ = lean_ctor_get(v_m_1708_, 0);
v_buckets_1712_ = lean_ctor_get(v_m_1708_, 1);
v_isSharedCheck_1755_ = !lean_is_exclusive(v_m_1708_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1714_ = v_m_1708_;
v_isShared_1715_ = v_isSharedCheck_1755_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_buckets_1712_);
lean_inc(v_size_1711_);
lean_dec(v_m_1708_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1755_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1716_; uint64_t v___x_1717_; uint64_t v___x_1718_; uint64_t v___x_1719_; uint64_t v_fold_1720_; uint64_t v___x_1721_; uint64_t v___x_1722_; uint64_t v___x_1723_; size_t v___x_1724_; size_t v___x_1725_; size_t v___x_1726_; size_t v___x_1727_; size_t v___x_1728_; lean_object* v_bkt_1729_; uint8_t v___x_1730_; 
v___x_1716_ = lean_array_get_size(v_buckets_1712_);
v___x_1717_ = lean_uint64_of_nat(v_a_1709_);
v___x_1718_ = 32ULL;
v___x_1719_ = lean_uint64_shift_right(v___x_1717_, v___x_1718_);
v_fold_1720_ = lean_uint64_xor(v___x_1717_, v___x_1719_);
v___x_1721_ = 16ULL;
v___x_1722_ = lean_uint64_shift_right(v_fold_1720_, v___x_1721_);
v___x_1723_ = lean_uint64_xor(v_fold_1720_, v___x_1722_);
v___x_1724_ = lean_uint64_to_usize(v___x_1723_);
v___x_1725_ = lean_usize_of_nat(v___x_1716_);
v___x_1726_ = ((size_t)1ULL);
v___x_1727_ = lean_usize_sub(v___x_1725_, v___x_1726_);
v___x_1728_ = lean_usize_land(v___x_1724_, v___x_1727_);
v_bkt_1729_ = lean_array_uget_borrowed(v_buckets_1712_, v___x_1728_);
v___x_1730_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__2___redArg(v_a_1709_, v_bkt_1729_);
if (v___x_1730_ == 0)
{
lean_object* v___x_1731_; lean_object* v_size_x27_1732_; lean_object* v___x_1733_; lean_object* v_buckets_x27_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; uint8_t v___x_1740_; 
v___x_1731_ = lean_unsigned_to_nat(1u);
v_size_x27_1732_ = lean_nat_add(v_size_1711_, v___x_1731_);
lean_dec(v_size_1711_);
lean_inc(v_bkt_1729_);
v___x_1733_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1733_, 0, v_a_1709_);
lean_ctor_set(v___x_1733_, 1, v_b_1710_);
lean_ctor_set(v___x_1733_, 2, v_bkt_1729_);
v_buckets_x27_1734_ = lean_array_uset(v_buckets_1712_, v___x_1728_, v___x_1733_);
v___x_1735_ = lean_unsigned_to_nat(4u);
v___x_1736_ = lean_nat_mul(v_size_x27_1732_, v___x_1735_);
v___x_1737_ = lean_unsigned_to_nat(3u);
v___x_1738_ = lean_nat_div(v___x_1736_, v___x_1737_);
lean_dec(v___x_1736_);
v___x_1739_ = lean_array_get_size(v_buckets_x27_1734_);
v___x_1740_ = lean_nat_dec_le(v___x_1738_, v___x_1739_);
lean_dec(v___x_1738_);
if (v___x_1740_ == 0)
{
lean_object* v_val_1741_; lean_object* v___x_1743_; 
v_val_1741_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__3___redArg(v_buckets_x27_1734_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 1, v_val_1741_);
lean_ctor_set(v___x_1714_, 0, v_size_x27_1732_);
v___x_1743_ = v___x_1714_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_size_x27_1732_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_val_1741_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
else
{
lean_object* v___x_1746_; 
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 1, v_buckets_x27_1734_);
lean_ctor_set(v___x_1714_, 0, v_size_x27_1732_);
v___x_1746_ = v___x_1714_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_size_x27_1732_);
lean_ctor_set(v_reuseFailAlloc_1747_, 1, v_buckets_x27_1734_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
else
{
lean_object* v___x_1748_; lean_object* v_buckets_x27_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1753_; 
lean_inc(v_bkt_1729_);
v___x_1748_ = lean_box(0);
v_buckets_x27_1749_ = lean_array_uset(v_buckets_1712_, v___x_1728_, v___x_1748_);
v___x_1750_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__4___redArg(v_a_1709_, v_b_1710_, v_bkt_1729_);
v___x_1751_ = lean_array_uset(v_buckets_x27_1749_, v___x_1728_, v___x_1750_);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 1, v___x_1751_);
v___x_1753_ = v___x_1714_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_size_1711_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v___x_1751_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__2___redArg(lean_object* v_as_x27_1756_, lean_object* v_b_1757_){
_start:
{
if (lean_obj_tag(v_as_x27_1756_) == 0)
{
return v_b_1757_;
}
else
{
lean_object* v_head_1758_; lean_object* v_tail_1759_; lean_object* v_fst_1760_; lean_object* v_snd_1761_; lean_object* v_r_1762_; 
v_head_1758_ = lean_ctor_get(v_as_x27_1756_, 0);
v_tail_1759_ = lean_ctor_get(v_as_x27_1756_, 1);
v_fst_1760_ = lean_ctor_get(v_head_1758_, 0);
v_snd_1761_ = lean_ctor_get(v_head_1758_, 1);
lean_inc(v_snd_1761_);
lean_inc(v_fst_1760_);
v_r_1762_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1___redArg(v_b_1757_, v_fst_1760_, v_snd_1761_);
v_as_x27_1756_ = v_tail_1759_;
v_b_1757_ = v_r_1762_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__2___redArg___boxed(lean_object* v_as_x27_1764_, lean_object* v_b_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__2___redArg(v_as_x27_1764_, v_b_1765_);
lean_dec(v_as_x27_1764_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1(lean_object* v_m_1767_, lean_object* v_l_1768_){
_start:
{
lean_object* v___x_1769_; 
v___x_1769_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__2___redArg(v_l_1768_, v_m_1767_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1___boxed(lean_object* v_m_1770_, lean_object* v_l_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1(v_m_1770_, v_l_1771_);
lean_dec(v_l_1771_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__2(lean_object* v_x_1773_, lean_object* v_x_1774_){
_start:
{
if (lean_obj_tag(v_x_1774_) == 0)
{
lean_inc(v_x_1773_);
return v_x_1773_;
}
else
{
lean_object* v_key_1775_; lean_object* v_value_1776_; lean_object* v_tail_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; 
v_key_1775_ = lean_ctor_get(v_x_1774_, 0);
v_value_1776_ = lean_ctor_get(v_x_1774_, 1);
v_tail_1777_ = lean_ctor_get(v_x_1774_, 2);
v___x_1778_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__2(v_x_1773_, v_tail_1777_);
lean_inc(v_value_1776_);
lean_inc(v_key_1775_);
v___x_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1779_, 0, v_key_1775_);
lean_ctor_set(v___x_1779_, 1, v_value_1776_);
v___x_1780_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1779_);
lean_ctor_set(v___x_1780_, 1, v___x_1778_);
return v___x_1780_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__2___boxed(lean_object* v_x_1781_, lean_object* v_x_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__2(v_x_1781_, v_x_1782_);
lean_dec(v_x_1782_);
lean_dec(v_x_1781_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__3(lean_object* v_as_1784_, size_t v_i_1785_, size_t v_stop_1786_, lean_object* v_b_1787_){
_start:
{
uint8_t v___x_1788_; 
v___x_1788_ = lean_usize_dec_eq(v_i_1785_, v_stop_1786_);
if (v___x_1788_ == 0)
{
size_t v___x_1789_; size_t v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1789_ = ((size_t)1ULL);
v___x_1790_ = lean_usize_sub(v_i_1785_, v___x_1789_);
v___x_1791_ = lean_array_uget_borrowed(v_as_1784_, v___x_1790_);
v___x_1792_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__2(v_b_1787_, v___x_1791_);
lean_dec(v_b_1787_);
v_i_1785_ = v___x_1790_;
v_b_1787_ = v___x_1792_;
goto _start;
}
else
{
return v_b_1787_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__3___boxed(lean_object* v_as_1794_, lean_object* v_i_1795_, lean_object* v_stop_1796_, lean_object* v_b_1797_){
_start:
{
size_t v_i_boxed_1798_; size_t v_stop_boxed_1799_; lean_object* v_res_1800_; 
v_i_boxed_1798_ = lean_unbox_usize(v_i_1795_);
lean_dec(v_i_1795_);
v_stop_boxed_1799_ = lean_unbox_usize(v_stop_1796_);
lean_dec(v_stop_1796_);
v_res_1800_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__3(v_as_1794_, v_i_boxed_1798_, v_stop_boxed_1799_, v_b_1797_);
lean_dec_ref(v_as_1794_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__0(lean_object* v_a_1801_, lean_object* v_a_1802_){
_start:
{
if (lean_obj_tag(v_a_1801_) == 0)
{
lean_object* v___x_1803_; 
v___x_1803_ = l_List_reverse___redArg(v_a_1802_);
return v___x_1803_;
}
else
{
lean_object* v_head_1804_; lean_object* v_snd_1805_; lean_object* v_tail_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1829_; 
v_head_1804_ = lean_ctor_get(v_a_1801_, 0);
lean_inc(v_head_1804_);
v_snd_1805_ = lean_ctor_get(v_head_1804_, 1);
lean_inc(v_snd_1805_);
v_tail_1806_ = lean_ctor_get(v_a_1801_, 1);
v_isSharedCheck_1829_ = !lean_is_exclusive(v_a_1801_);
if (v_isSharedCheck_1829_ == 0)
{
lean_object* v_unused_1830_; 
v_unused_1830_ = lean_ctor_get(v_a_1801_, 0);
lean_dec(v_unused_1830_);
v___x_1808_ = v_a_1801_;
v_isShared_1809_ = v_isSharedCheck_1829_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_tail_1806_);
lean_dec(v_a_1801_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1829_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v_fst_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1827_; 
v_fst_1810_ = lean_ctor_get(v_head_1804_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v_head_1804_);
if (v_isSharedCheck_1827_ == 0)
{
lean_object* v_unused_1828_; 
v_unused_1828_ = lean_ctor_get(v_head_1804_, 1);
lean_dec(v_unused_1828_);
v___x_1812_ = v_head_1804_;
v_isShared_1813_ = v_isSharedCheck_1827_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_fst_1810_);
lean_dec(v_head_1804_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1827_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v_width_1814_; lean_object* v_atomNumber_1815_; uint8_t v_synthetic_1816_; lean_object* v___x_1817_; lean_object* v___x_1819_; 
v_width_1814_ = lean_ctor_get(v_snd_1805_, 0);
lean_inc(v_width_1814_);
v_atomNumber_1815_ = lean_ctor_get(v_snd_1805_, 1);
lean_inc(v_atomNumber_1815_);
v_synthetic_1816_ = lean_ctor_get_uint8(v_snd_1805_, sizeof(void*)*2);
lean_dec(v_snd_1805_);
v___x_1817_ = lean_box(v_synthetic_1816_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 1, v___x_1817_);
v___x_1819_ = v___x_1812_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_fst_1810_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1823_; 
v___x_1820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1820_, 0, v_width_1814_);
lean_ctor_set(v___x_1820_, 1, v___x_1819_);
v___x_1821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1821_, 0, v_atomNumber_1815_);
lean_ctor_set(v___x_1821_, 1, v___x_1820_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 1, v_a_1802_);
lean_ctor_set(v___x_1808_, 0, v___x_1821_);
v___x_1823_ = v___x_1808_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v___x_1821_);
lean_ctor_set(v_reuseFailAlloc_1825_, 1, v_a_1802_);
v___x_1823_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
v_a_1801_ = v_tail_1806_;
v_a_1802_ = v___x_1823_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg___closed__0(void){
_start:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1831_ = lean_box(0);
v___x_1832_ = lean_unsigned_to_nat(16u);
v___x_1833_ = lean_mk_array(v___x_1832_, v___x_1831_);
return v___x_1833_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg___closed__1(void){
_start:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1834_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg___closed__0);
v___x_1835_ = lean_unsigned_to_nat(0u);
v___x_1836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
lean_ctor_set(v___x_1836_, 1, v___x_1834_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg(lean_object* v_a_1837_){
_start:
{
lean_object* v___x_1839_; lean_object* v___y_1841_; lean_object* v_atoms_1862_; lean_object* v_buckets_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; 
v___x_1839_ = lean_st_ref_get(v_a_1837_);
v_atoms_1862_ = lean_ctor_get(v___x_1839_, 0);
lean_inc_ref(v_atoms_1862_);
lean_dec(v___x_1839_);
v_buckets_1863_ = lean_ctor_get(v_atoms_1862_, 1);
lean_inc_ref(v_buckets_1863_);
lean_dec_ref(v_atoms_1862_);
v___x_1864_ = lean_box(0);
v___x_1865_ = lean_array_get_size(v_buckets_1863_);
v___x_1866_ = lean_unsigned_to_nat(0u);
v___x_1867_ = lean_nat_dec_lt(v___x_1866_, v___x_1865_);
if (v___x_1867_ == 0)
{
lean_dec_ref(v_buckets_1863_);
v___y_1841_ = v___x_1864_;
goto v___jp_1840_;
}
else
{
size_t v___x_1868_; size_t v___x_1869_; lean_object* v___x_1870_; 
v___x_1868_ = lean_usize_of_nat(v___x_1865_);
v___x_1869_ = ((size_t)0ULL);
v___x_1870_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__3(v_buckets_1863_, v___x_1868_, v___x_1869_, v___x_1864_);
lean_dec_ref(v_buckets_1863_);
v___y_1841_ = v___x_1870_;
goto v___jp_1840_;
}
v___jp_1840_:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v_atoms_1847_; lean_object* v_atomsAssignmentExprCache_1848_; lean_object* v_evalsAtCache_1849_; lean_object* v_theoryState_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1860_; 
v___x_1842_ = lean_box(0);
v___x_1843_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__0(v___y_1841_, v___x_1842_);
v___x_1844_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg___closed__1);
v___x_1845_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__2___redArg(v___x_1843_, v___x_1844_);
lean_dec(v___x_1843_);
v___x_1846_ = lean_st_ref_take(v_a_1837_);
v_atoms_1847_ = lean_ctor_get(v___x_1846_, 0);
v_atomsAssignmentExprCache_1848_ = lean_ctor_get(v___x_1846_, 1);
v_evalsAtCache_1849_ = lean_ctor_get(v___x_1846_, 3);
v_theoryState_1850_ = lean_ctor_get(v___x_1846_, 4);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1860_ == 0)
{
lean_object* v_unused_1861_; 
v_unused_1861_ = lean_ctor_get(v___x_1846_, 2);
lean_dec(v_unused_1861_);
v___x_1852_ = v___x_1846_;
v_isShared_1853_ = v_isSharedCheck_1860_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_theoryState_1850_);
lean_inc(v_evalsAtCache_1849_);
lean_inc(v_atomsAssignmentExprCache_1848_);
lean_inc(v_atoms_1847_);
lean_dec(v___x_1846_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1860_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1854_; lean_object* v___x_1856_; 
lean_inc_ref(v___x_1845_);
v___x_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1845_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 2, v___x_1854_);
v___x_1856_ = v___x_1852_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_atoms_1847_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_atomsAssignmentExprCache_1848_);
lean_ctor_set(v_reuseFailAlloc_1859_, 2, v___x_1854_);
lean_ctor_set(v_reuseFailAlloc_1859_, 3, v_evalsAtCache_1849_);
lean_ctor_set(v_reuseFailAlloc_1859_, 4, v_theoryState_1850_);
v___x_1856_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = lean_st_ref_put(v_a_1837_, v___x_1856_);
v___x_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1845_);
return v___x_1858_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg___boxed(lean_object* v_a_1871_, lean_object* v_a_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg(v_a_1871_);
lean_dec(v_a_1871_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment(lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg(v_a_1875_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___boxed(lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment(v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_);
lean_dec(v_a_1897_);
lean_dec_ref(v_a_1896_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
lean_dec(v_a_1893_);
lean_dec_ref(v_a_1892_);
lean_dec(v_a_1891_);
lean_dec_ref(v_a_1890_);
lean_dec(v_a_1889_);
lean_dec(v_a_1888_);
lean_dec_ref(v_a_1887_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1(lean_object* v_00_u03b2_1900_, lean_object* v_m_1901_, lean_object* v_a_1902_, lean_object* v_b_1903_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1___redArg(v_m_1901_, v_a_1902_, v_b_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__2(lean_object* v_as_1905_, lean_object* v_as_x27_1906_, lean_object* v_b_1907_, lean_object* v_a_1908_){
_start:
{
lean_object* v___x_1909_; 
v___x_1909_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__2___redArg(v_as_x27_1906_, v_b_1907_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__2___boxed(lean_object* v_as_1910_, lean_object* v_as_x27_1911_, lean_object* v_b_1912_, lean_object* v_a_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__2(v_as_1910_, v_as_x27_1911_, v_b_1912_, v_a_1913_);
lean_dec(v_as_x27_1911_);
lean_dec(v_as_1910_);
return v_res_1914_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1915_, lean_object* v_a_1916_, lean_object* v_x_1917_){
_start:
{
uint8_t v___x_1918_; 
v___x_1918_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__2___redArg(v_a_1916_, v_x_1917_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1919_, lean_object* v_a_1920_, lean_object* v_x_1921_){
_start:
{
uint8_t v_res_1922_; lean_object* v_r_1923_; 
v_res_1922_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__2(v_00_u03b2_1919_, v_a_1920_, v_x_1921_);
lean_dec(v_x_1921_);
lean_dec(v_a_1920_);
v_r_1923_ = lean_box(v_res_1922_);
return v_r_1923_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_1924_, lean_object* v_data_1925_){
_start:
{
lean_object* v___x_1926_; 
v___x_1926_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__3___redArg(v_data_1925_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_1927_, lean_object* v_a_1928_, lean_object* v_b_1929_, lean_object* v_x_1930_){
_start:
{
lean_object* v___x_1931_; 
v___x_1931_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__4___redArg(v_a_1928_, v_b_1929_, v_x_1930_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_1932_, lean_object* v_i_1933_, lean_object* v_source_1934_, lean_object* v_target_1935_){
_start:
{
lean_object* v___x_1936_; 
v___x_1936_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__3_spec__6___redArg(v_i_1933_, v_source_1934_, v_target_1935_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_1937_, lean_object* v_x_1938_, lean_object* v_x_1939_){
_start:
{
lean_object* v___x_1940_; 
v___x_1940_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__3_spec__6_spec__8___redArg(v_x_1938_, v_x_1939_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(lean_object* v_a_1941_){
_start:
{
lean_object* v___x_1943_; lean_object* v_atomsAssignmentMapCache_1944_; 
v___x_1943_ = lean_st_ref_get(v_a_1941_);
v_atomsAssignmentMapCache_1944_ = lean_ctor_get(v___x_1943_, 2);
lean_inc(v_atomsAssignmentMapCache_1944_);
lean_dec(v___x_1943_);
if (lean_obj_tag(v_atomsAssignmentMapCache_1944_) == 0)
{
lean_object* v___x_1945_; 
v___x_1945_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg(v_a_1941_);
return v___x_1945_;
}
else
{
lean_object* v_val_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
v_val_1946_ = lean_ctor_get(v_atomsAssignmentMapCache_1944_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v_atomsAssignmentMapCache_1944_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v_atomsAssignmentMapCache_1944_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_val_1946_);
lean_dec(v_atomsAssignmentMapCache_1944_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
lean_ctor_set_tag(v___x_1948_, 0);
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_val_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg___boxed(lean_object* v_a_1954_, lean_object* v_a_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(v_a_1954_);
lean_dec(v_a_1954_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap(lean_object* v_a_1957_, lean_object* v_a_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_){
_start:
{
lean_object* v___x_1969_; 
v___x_1969_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(v_a_1958_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___boxed(lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap(v_a_1970_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_, v_a_1980_);
lean_dec(v_a_1980_);
lean_dec_ref(v_a_1979_);
lean_dec(v_a_1978_);
lean_dec_ref(v_a_1977_);
lean_dec(v_a_1976_);
lean_dec_ref(v_a_1975_);
lean_dec(v_a_1974_);
lean_dec_ref(v_a_1973_);
lean_dec(v_a_1972_);
lean_dec(v_a_1971_);
lean_dec_ref(v_a_1970_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___lam__0(lean_object* v___x_1984_, lean_object* v___x_1985_, lean_object* v___x_1986_, lean_object* v___x_1987_, lean_object* v___x_1988_, lean_object* v___x_1989_, lean_object* v_x_1990_){
_start:
{
lean_object* v_fst_1991_; lean_object* v_snd_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v_fst_1991_ = lean_ctor_get(v_x_1990_, 0);
lean_inc(v_fst_1991_);
v_snd_1992_ = lean_ctor_get(v_x_1990_, 1);
lean_inc(v_snd_1992_);
lean_dec_ref(v_x_1990_);
v___x_1993_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___lam__0___closed__0));
v___x_1994_ = l_Lean_Name_mkStr6(v___x_1984_, v___x_1985_, v___x_1986_, v___x_1987_, v___x_1988_, v___x_1993_);
v___x_1995_ = l_Lean_mkConst(v___x_1994_, v___x_1989_);
v___x_1996_ = l_Lean_mkNatLit(v_fst_1991_);
v___x_1997_ = l_Lean_mkAppB(v___x_1995_, v___x_1996_, v_snd_1992_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0_spec__0(lean_object* v_msgData_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v___x_2004_; lean_object* v_env_2005_; uint8_t v___x_2006_; lean_object* v_env_2007_; lean_object* v___x_2008_; lean_object* v_toCold_2009_; lean_object* v_mctx_2010_; lean_object* v_lctx_2011_; lean_object* v_options_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2004_ = lean_st_ref_get(v___y_2002_);
v_env_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc_ref(v_env_2005_);
lean_dec(v___x_2004_);
v___x_2006_ = 0;
v_env_2007_ = l_Lean_Environment_setRecordingDeps(v_env_2005_, v___x_2006_);
v___x_2008_ = lean_st_ref_get(v___y_2000_);
v_toCold_2009_ = lean_ctor_get(v___y_2001_, 0);
v_mctx_2010_ = lean_ctor_get(v___x_2008_, 0);
lean_inc_ref(v_mctx_2010_);
lean_dec(v___x_2008_);
v_lctx_2011_ = lean_ctor_get(v___y_1999_, 2);
v_options_2012_ = lean_ctor_get(v_toCold_2009_, 2);
lean_inc_ref(v_options_2012_);
lean_inc_ref(v_lctx_2011_);
v___x_2013_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2013_, 0, v_env_2007_);
lean_ctor_set(v___x_2013_, 1, v_mctx_2010_);
lean_ctor_set(v___x_2013_, 2, v_lctx_2011_);
lean_ctor_set(v___x_2013_, 3, v_options_2012_);
v___x_2014_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2014_, 0, v___x_2013_);
lean_ctor_set(v___x_2014_, 1, v_msgData_1998_);
v___x_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2014_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0_spec__0___boxed(lean_object* v_msgData_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0_spec__0(v_msgData_2016_, v___y_2017_, v___y_2018_, v___y_2019_, v___y_2020_);
lean_dec(v___y_2020_);
lean_dec_ref(v___y_2019_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0___redArg(lean_object* v_msg_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_){
_start:
{
lean_object* v_ref_2029_; lean_object* v___x_2030_; lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2039_; 
v_ref_2029_ = lean_ctor_get(v___y_2026_, 2);
v___x_2030_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0_spec__0(v_msg_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2033_ = v___x_2030_;
v_isShared_2034_ = v_isSharedCheck_2039_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2030_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2039_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2035_; lean_object* v___x_2037_; 
lean_inc(v_ref_2029_);
v___x_2035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2035_, 0, v_ref_2029_);
lean_ctor_set(v___x_2035_, 1, v_a_2031_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set_tag(v___x_2033_, 1);
lean_ctor_set(v___x_2033_, 0, v___x_2035_);
v___x_2037_ = v___x_2033_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0___redArg___boxed(lean_object* v_msg_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0___redArg(v_msg_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
lean_dec(v___y_2044_);
lean_dec_ref(v___y_2043_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
return v_res_2046_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__1(void){
_start:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__0));
v___x_2049_ = l_Lean_stringToMessageData(v___x_2048_);
return v___x_2049_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__5(void){
_start:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2064_ = lean_box(0);
v___x_2065_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__3));
v___x_2066_ = l_Lean_mkConst(v___x_2065_, v___x_2064_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment(lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_){
_start:
{
lean_object* v___x_2079_; lean_object* v_a_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; uint8_t v___x_2083_; 
v___x_2079_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atoms___redArg(v_a_2068_);
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_a_2080_);
lean_dec_ref(v___x_2079_);
v___x_2081_ = lean_unsigned_to_nat(0u);
v___x_2082_ = lean_array_get_size(v_a_2080_);
v___x_2083_ = lean_nat_dec_lt(v___x_2081_, v___x_2082_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
lean_dec(v_a_2080_);
v___x_2084_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__1);
v___x_2085_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0___redArg(v___x_2084_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
return v___x_2085_;
}
else
{
lean_object* v___x_2086_; lean_object* v___f_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2086_ = l_Lean_RArray_ofArray___redArg(v_a_2080_);
v___f_2087_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__4));
v___x_2088_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__5, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__5_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__5);
v___x_2089_ = l_Lean_RArray_toExpr___redArg(v___x_2088_, v___f_2087_, v___x_2086_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2120_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2092_ = v___x_2089_;
v_isShared_2093_ = v_isSharedCheck_2120_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2089_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2120_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; 
v___x_2094_ = l_Lean_Meta_Sym_shareCommon(v_a_2090_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2119_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2119_ == 0)
{
v___x_2097_ = v___x_2094_;
v_isShared_2098_ = v_isSharedCheck_2119_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2094_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2119_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2099_; lean_object* v_atoms_2100_; lean_object* v_atomsAssignmentMapCache_2101_; lean_object* v_evalsAtCache_2102_; lean_object* v_theoryState_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2117_; 
v___x_2099_ = lean_st_ref_take(v_a_2068_);
v_atoms_2100_ = lean_ctor_get(v___x_2099_, 0);
v_atomsAssignmentMapCache_2101_ = lean_ctor_get(v___x_2099_, 2);
v_evalsAtCache_2102_ = lean_ctor_get(v___x_2099_, 3);
v_theoryState_2103_ = lean_ctor_get(v___x_2099_, 4);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2117_ == 0)
{
lean_object* v_unused_2118_; 
v_unused_2118_ = lean_ctor_get(v___x_2099_, 1);
lean_dec(v_unused_2118_);
v___x_2105_ = v___x_2099_;
v_isShared_2106_ = v_isSharedCheck_2117_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_theoryState_2103_);
lean_inc(v_evalsAtCache_2102_);
lean_inc(v_atomsAssignmentMapCache_2101_);
lean_inc(v_atoms_2100_);
lean_dec(v___x_2099_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2117_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
lean_inc(v_a_2095_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set_tag(v___x_2092_, 1);
lean_ctor_set(v___x_2092_, 0, v_a_2095_);
v___x_2108_ = v___x_2092_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2095_);
v___x_2108_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
lean_object* v___x_2110_; 
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 1, v___x_2108_);
v___x_2110_ = v___x_2105_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_atoms_2100_);
lean_ctor_set(v_reuseFailAlloc_2115_, 1, v___x_2108_);
lean_ctor_set(v_reuseFailAlloc_2115_, 2, v_atomsAssignmentMapCache_2101_);
lean_ctor_set(v_reuseFailAlloc_2115_, 3, v_evalsAtCache_2102_);
lean_ctor_set(v_reuseFailAlloc_2115_, 4, v_theoryState_2103_);
v___x_2110_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
lean_object* v___x_2111_; lean_object* v___x_2113_; 
v___x_2111_ = lean_st_ref_put(v_a_2068_, v___x_2110_);
if (v_isShared_2098_ == 0)
{
v___x_2113_ = v___x_2097_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_a_2095_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_2092_);
return v___x_2094_;
}
}
}
else
{
return v___x_2089_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___boxed(lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment(v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_);
lean_dec(v_a_2131_);
lean_dec_ref(v_a_2130_);
lean_dec(v_a_2129_);
lean_dec_ref(v_a_2128_);
lean_dec(v_a_2127_);
lean_dec_ref(v_a_2126_);
lean_dec(v_a_2125_);
lean_dec_ref(v_a_2124_);
lean_dec(v_a_2123_);
lean_dec(v_a_2122_);
lean_dec_ref(v_a_2121_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0(lean_object* v_00_u03b1_2134_, lean_object* v_msg_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v___x_2148_; 
v___x_2148_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0___redArg(v_msg_2135_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0___boxed(lean_object* v_00_u03b1_2149_, lean_object* v_msg_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0(v_00_u03b1_2149_, v_msg_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr(lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_a_2173_, lean_object* v_a_2174_){
_start:
{
lean_object* v___x_2176_; lean_object* v_atomsAssignmentExprCache_2177_; 
v___x_2176_ = lean_st_ref_get(v_a_2165_);
v_atomsAssignmentExprCache_2177_ = lean_ctor_get(v___x_2176_, 1);
lean_inc(v_atomsAssignmentExprCache_2177_);
lean_dec(v___x_2176_);
if (lean_obj_tag(v_atomsAssignmentExprCache_2177_) == 0)
{
lean_object* v___x_2178_; 
v___x_2178_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment(v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_);
return v___x_2178_;
}
else
{
lean_object* v_val_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
v_val_2179_ = lean_ctor_get(v_atomsAssignmentExprCache_2177_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v_atomsAssignmentExprCache_2177_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v_atomsAssignmentExprCache_2177_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_val_2179_);
lean_dec(v_atomsAssignmentExprCache_2177_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
lean_ctor_set_tag(v___x_2181_, 0);
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_val_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr___boxed(lean_object* v_a_2187_, lean_object* v_a_2188_, lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr(v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_);
lean_dec(v_a_2197_);
lean_dec_ref(v_a_2196_);
lean_dec(v_a_2195_);
lean_dec_ref(v_a_2194_);
lean_dec(v_a_2193_);
lean_dec_ref(v_a_2192_);
lean_dec(v_a_2191_);
lean_dec_ref(v_a_2190_);
lean_dec(v_a_2189_);
lean_dec(v_a_2188_);
lean_dec_ref(v_a_2187_);
return v_res_2199_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_ReifyM_isAtom_spec__0___redArg(lean_object* v_m_2200_, lean_object* v_a_2201_){
_start:
{
lean_object* v_buckets_2202_; lean_object* v___x_2203_; size_t v___x_2204_; size_t v___x_2205_; size_t v___x_2206_; uint64_t v___x_2207_; uint64_t v___x_2208_; uint64_t v___x_2209_; uint64_t v_fold_2210_; uint64_t v___x_2211_; uint64_t v___x_2212_; uint64_t v___x_2213_; size_t v___x_2214_; size_t v___x_2215_; size_t v___x_2216_; size_t v___x_2217_; size_t v___x_2218_; lean_object* v___x_2219_; uint8_t v___x_2220_; 
v_buckets_2202_ = lean_ctor_get(v_m_2200_, 1);
v___x_2203_ = lean_array_get_size(v_buckets_2202_);
v___x_2204_ = lean_ptr_addr(v_a_2201_);
v___x_2205_ = ((size_t)3ULL);
v___x_2206_ = lean_usize_shift_right(v___x_2204_, v___x_2205_);
v___x_2207_ = lean_usize_to_uint64(v___x_2206_);
v___x_2208_ = 32ULL;
v___x_2209_ = lean_uint64_shift_right(v___x_2207_, v___x_2208_);
v_fold_2210_ = lean_uint64_xor(v___x_2207_, v___x_2209_);
v___x_2211_ = 16ULL;
v___x_2212_ = lean_uint64_shift_right(v_fold_2210_, v___x_2211_);
v___x_2213_ = lean_uint64_xor(v_fold_2210_, v___x_2212_);
v___x_2214_ = lean_uint64_to_usize(v___x_2213_);
v___x_2215_ = lean_usize_of_nat(v___x_2203_);
v___x_2216_ = ((size_t)1ULL);
v___x_2217_ = lean_usize_sub(v___x_2215_, v___x_2216_);
v___x_2218_ = lean_usize_land(v___x_2214_, v___x_2217_);
v___x_2219_ = lean_array_uget_borrowed(v_buckets_2202_, v___x_2218_);
v___x_2220_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg(v_a_2201_, v___x_2219_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_ReifyM_isAtom_spec__0___redArg___boxed(lean_object* v_m_2221_, lean_object* v_a_2222_){
_start:
{
uint8_t v_res_2223_; lean_object* v_r_2224_; 
v_res_2223_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_ReifyM_isAtom_spec__0___redArg(v_m_2221_, v_a_2222_);
lean_dec_ref(v_a_2222_);
lean_dec_ref(v_m_2221_);
v_r_2224_ = lean_box(v_res_2223_);
return v_r_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_isAtom___redArg(lean_object* v_e_2225_, lean_object* v_a_2226_){
_start:
{
lean_object* v___x_2228_; lean_object* v_atoms_2229_; uint8_t v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2228_ = lean_st_ref_get(v_a_2226_);
v_atoms_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc_ref(v_atoms_2229_);
lean_dec(v___x_2228_);
v___x_2230_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_ReifyM_isAtom_spec__0___redArg(v_atoms_2229_, v_e_2225_);
lean_dec_ref(v_atoms_2229_);
v___x_2231_ = lean_box(v___x_2230_);
v___x_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_isAtom___redArg___boxed(lean_object* v_e_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_isAtom___redArg(v_e_2233_, v_a_2234_);
lean_dec(v_a_2234_);
lean_dec_ref(v_e_2233_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_isAtom(lean_object* v_e_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_isAtom___redArg(v_e_2237_, v_a_2239_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_isAtom___boxed(lean_object* v_e_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_isAtom(v_e_2251_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_);
lean_dec(v_a_2262_);
lean_dec_ref(v_a_2261_);
lean_dec(v_a_2260_);
lean_dec_ref(v_a_2259_);
lean_dec(v_a_2258_);
lean_dec_ref(v_a_2257_);
lean_dec(v_a_2256_);
lean_dec_ref(v_a_2255_);
lean_dec(v_a_2254_);
lean_dec(v_a_2253_);
lean_dec_ref(v_a_2252_);
lean_dec_ref(v_e_2251_);
return v_res_2264_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_ReifyM_isAtom_spec__0(lean_object* v_00_u03b2_2265_, lean_object* v_m_2266_, lean_object* v_a_2267_){
_start:
{
uint8_t v___x_2268_; 
v___x_2268_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_ReifyM_isAtom_spec__0___redArg(v_m_2266_, v_a_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_ReifyM_isAtom_spec__0___boxed(lean_object* v_00_u03b2_2269_, lean_object* v_m_2270_, lean_object* v_a_2271_){
_start:
{
uint8_t v_res_2272_; lean_object* v_r_2273_; 
v_res_2272_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_ReifyM_isAtom_spec__0(v_00_u03b2_2269_, v_m_2270_, v_a_2271_);
lean_dec_ref(v_a_2271_);
lean_dec_ref(v_m_2270_);
v_r_2273_ = lean_box(v_res_2272_);
return v_r_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_getAtomNumber___redArg(lean_object* v_e_2274_, lean_object* v_a_2275_){
_start:
{
lean_object* v___x_2277_; lean_object* v_atoms_2278_; lean_object* v___x_2279_; 
v___x_2277_ = lean_st_ref_get(v_a_2275_);
v_atoms_2278_ = lean_ctor_get(v___x_2277_, 0);
lean_inc_ref(v_atoms_2278_);
lean_dec(v___x_2277_);
v___x_2279_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_atoms_2278_, v_e_2274_);
lean_dec_ref(v_atoms_2278_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2280_ = lean_box(0);
v___x_2281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2280_);
return v___x_2281_;
}
else
{
lean_object* v_val_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2291_; 
v_val_2282_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2284_ = v___x_2279_;
v_isShared_2285_ = v_isSharedCheck_2291_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_val_2282_);
lean_dec(v___x_2279_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2291_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v_atomNumber_2286_; lean_object* v___x_2288_; 
v_atomNumber_2286_ = lean_ctor_get(v_val_2282_, 1);
lean_inc(v_atomNumber_2286_);
lean_dec(v_val_2282_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 0, v_atomNumber_2286_);
v___x_2288_ = v___x_2284_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_atomNumber_2286_);
v___x_2288_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
lean_object* v___x_2289_; 
v___x_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
return v___x_2289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_getAtomNumber___redArg___boxed(lean_object* v_e_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_getAtomNumber___redArg(v_e_2292_, v_a_2293_);
lean_dec(v_a_2293_);
lean_dec_ref(v_e_2292_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_getAtomNumber(lean_object* v_e_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_){
_start:
{
lean_object* v___x_2309_; 
v___x_2309_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_getAtomNumber___redArg(v_e_2296_, v_a_2298_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_getAtomNumber___boxed(lean_object* v_e_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_getAtomNumber(v_e_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_);
lean_dec(v_a_2321_);
lean_dec_ref(v_a_2320_);
lean_dec(v_a_2319_);
lean_dec_ref(v_a_2318_);
lean_dec(v_a_2317_);
lean_dec_ref(v_a_2316_);
lean_dec(v_a_2315_);
lean_dec_ref(v_a_2314_);
lean_dec(v_a_2313_);
lean_dec(v_a_2312_);
lean_dec_ref(v_a_2311_);
lean_dec_ref(v_e_2310_);
return v_res_2323_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = l_instMonadEIO___redArg();
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1(lean_object* v_msg_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v_toApplicative_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2412_; 
v___x_2342_ = lean_obj_once(&l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___closed__0, &l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___closed__0);
v___x_2343_ = l_StateRefT_x27_instMonad___redArg(v___x_2342_);
v_toApplicative_2344_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2412_ == 0)
{
lean_object* v_unused_2413_; 
v_unused_2413_ = lean_ctor_get(v___x_2343_, 1);
lean_dec(v_unused_2413_);
v___x_2346_ = v___x_2343_;
v_isShared_2347_ = v_isSharedCheck_2412_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_toApplicative_2344_);
lean_dec(v___x_2343_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2412_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v_toFunctor_2348_; lean_object* v_toSeq_2349_; lean_object* v_toSeqLeft_2350_; lean_object* v_toSeqRight_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2410_; 
v_toFunctor_2348_ = lean_ctor_get(v_toApplicative_2344_, 0);
v_toSeq_2349_ = lean_ctor_get(v_toApplicative_2344_, 2);
v_toSeqLeft_2350_ = lean_ctor_get(v_toApplicative_2344_, 3);
v_toSeqRight_2351_ = lean_ctor_get(v_toApplicative_2344_, 4);
v_isSharedCheck_2410_ = !lean_is_exclusive(v_toApplicative_2344_);
if (v_isSharedCheck_2410_ == 0)
{
lean_object* v_unused_2411_; 
v_unused_2411_ = lean_ctor_get(v_toApplicative_2344_, 1);
lean_dec(v_unused_2411_);
v___x_2353_ = v_toApplicative_2344_;
v_isShared_2354_ = v_isSharedCheck_2410_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_toSeqRight_2351_);
lean_inc(v_toSeqLeft_2350_);
lean_inc(v_toSeq_2349_);
lean_inc(v_toFunctor_2348_);
lean_dec(v_toApplicative_2344_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2410_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___f_2355_; lean_object* v___f_2356_; lean_object* v___f_2357_; lean_object* v___f_2358_; lean_object* v___x_2359_; lean_object* v___f_2360_; lean_object* v___f_2361_; lean_object* v___f_2362_; lean_object* v___x_2364_; 
v___f_2355_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___closed__1));
v___f_2356_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___closed__2));
lean_inc_ref(v_toFunctor_2348_);
v___f_2357_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2357_, 0, v_toFunctor_2348_);
v___f_2358_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2358_, 0, v_toFunctor_2348_);
v___x_2359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___f_2357_);
lean_ctor_set(v___x_2359_, 1, v___f_2358_);
v___f_2360_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2360_, 0, v_toSeqRight_2351_);
v___f_2361_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2361_, 0, v_toSeqLeft_2350_);
v___f_2362_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2362_, 0, v_toSeq_2349_);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 4, v___f_2360_);
lean_ctor_set(v___x_2353_, 3, v___f_2361_);
lean_ctor_set(v___x_2353_, 2, v___f_2362_);
lean_ctor_set(v___x_2353_, 1, v___f_2355_);
lean_ctor_set(v___x_2353_, 0, v___x_2359_);
v___x_2364_ = v___x_2353_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2359_);
lean_ctor_set(v_reuseFailAlloc_2409_, 1, v___f_2355_);
lean_ctor_set(v_reuseFailAlloc_2409_, 2, v___f_2362_);
lean_ctor_set(v_reuseFailAlloc_2409_, 3, v___f_2361_);
lean_ctor_set(v_reuseFailAlloc_2409_, 4, v___f_2360_);
v___x_2364_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
lean_object* v___x_2366_; 
if (v_isShared_2347_ == 0)
{
lean_ctor_set(v___x_2346_, 1, v___f_2356_);
lean_ctor_set(v___x_2346_, 0, v___x_2364_);
v___x_2366_ = v___x_2346_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2364_);
lean_ctor_set(v_reuseFailAlloc_2408_, 1, v___f_2356_);
v___x_2366_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
lean_object* v___x_2367_; lean_object* v_toApplicative_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2406_; 
v___x_2367_ = l_StateRefT_x27_instMonad___redArg(v___x_2366_);
v_toApplicative_2368_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2406_ == 0)
{
lean_object* v_unused_2407_; 
v_unused_2407_ = lean_ctor_get(v___x_2367_, 1);
lean_dec(v_unused_2407_);
v___x_2370_ = v___x_2367_;
v_isShared_2371_ = v_isSharedCheck_2406_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_toApplicative_2368_);
lean_dec(v___x_2367_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2406_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v_toFunctor_2372_; lean_object* v_toSeq_2373_; lean_object* v_toSeqLeft_2374_; lean_object* v_toSeqRight_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2404_; 
v_toFunctor_2372_ = lean_ctor_get(v_toApplicative_2368_, 0);
v_toSeq_2373_ = lean_ctor_get(v_toApplicative_2368_, 2);
v_toSeqLeft_2374_ = lean_ctor_get(v_toApplicative_2368_, 3);
v_toSeqRight_2375_ = lean_ctor_get(v_toApplicative_2368_, 4);
v_isSharedCheck_2404_ = !lean_is_exclusive(v_toApplicative_2368_);
if (v_isSharedCheck_2404_ == 0)
{
lean_object* v_unused_2405_; 
v_unused_2405_ = lean_ctor_get(v_toApplicative_2368_, 1);
lean_dec(v_unused_2405_);
v___x_2377_ = v_toApplicative_2368_;
v_isShared_2378_ = v_isSharedCheck_2404_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_toSeqRight_2375_);
lean_inc(v_toSeqLeft_2374_);
lean_inc(v_toSeq_2373_);
lean_inc(v_toFunctor_2372_);
lean_dec(v_toApplicative_2368_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2404_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___f_2379_; lean_object* v___f_2380_; lean_object* v___f_2381_; lean_object* v___f_2382_; lean_object* v___x_2383_; lean_object* v___f_2384_; lean_object* v___f_2385_; lean_object* v___f_2386_; lean_object* v___x_2388_; 
v___f_2379_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___closed__3));
v___f_2380_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___closed__4));
lean_inc_ref(v_toFunctor_2372_);
v___f_2381_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2381_, 0, v_toFunctor_2372_);
v___f_2382_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2382_, 0, v_toFunctor_2372_);
v___x_2383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2383_, 0, v___f_2381_);
lean_ctor_set(v___x_2383_, 1, v___f_2382_);
v___f_2384_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2384_, 0, v_toSeqRight_2375_);
v___f_2385_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2385_, 0, v_toSeqLeft_2374_);
v___f_2386_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2386_, 0, v_toSeq_2373_);
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 4, v___f_2384_);
lean_ctor_set(v___x_2377_, 3, v___f_2385_);
lean_ctor_set(v___x_2377_, 2, v___f_2386_);
lean_ctor_set(v___x_2377_, 1, v___f_2379_);
lean_ctor_set(v___x_2377_, 0, v___x_2383_);
v___x_2388_ = v___x_2377_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v___x_2383_);
lean_ctor_set(v_reuseFailAlloc_2403_, 1, v___f_2379_);
lean_ctor_set(v_reuseFailAlloc_2403_, 2, v___f_2386_);
lean_ctor_set(v_reuseFailAlloc_2403_, 3, v___f_2385_);
lean_ctor_set(v_reuseFailAlloc_2403_, 4, v___f_2384_);
v___x_2388_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
lean_object* v___x_2390_; 
if (v_isShared_2371_ == 0)
{
lean_ctor_set(v___x_2370_, 1, v___f_2380_);
lean_ctor_set(v___x_2370_, 0, v___x_2388_);
v___x_2390_ = v___x_2370_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2388_);
lean_ctor_set(v_reuseFailAlloc_2402_, 1, v___f_2380_);
v___x_2390_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___f_2399_; lean_object* v___x_20328__overap_2400_; lean_object* v___x_2401_; 
v___x_2391_ = l_StateRefT_x27_instMonad___redArg(v___x_2390_);
v___x_2392_ = l_ReaderT_instMonad___redArg(v___x_2391_);
v___x_2393_ = l_StateRefT_x27_instMonad___redArg(v___x_2392_);
v___x_2394_ = l_ReaderT_instMonad___redArg(v___x_2393_);
v___x_2395_ = l_ReaderT_instMonad___redArg(v___x_2394_);
v___x_2396_ = l_StateRefT_x27_instMonad___redArg(v___x_2395_);
v___x_2397_ = lean_box(0);
v___x_2398_ = l_instInhabitedOfMonad___redArg(v___x_2396_, v___x_2397_);
v___f_2399_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2399_, 0, v___x_2398_);
v___x_20328__overap_2400_ = lean_panic_fn_borrowed(v___f_2399_, v_msg_2329_);
lean_dec_ref(v___f_2399_);
lean_inc(v___y_2340_);
lean_inc_ref(v___y_2339_);
lean_inc(v___y_2338_);
lean_inc_ref(v___y_2337_);
lean_inc(v___y_2336_);
lean_inc_ref(v___y_2335_);
lean_inc(v___y_2334_);
lean_inc_ref(v___y_2333_);
lean_inc(v___y_2332_);
lean_inc(v___y_2331_);
lean_inc_ref(v___y_2330_);
v___x_2401_ = lean_apply_12(v___x_20328__overap_2400_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, lean_box(0));
return v___x_2401_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___boxed(lean_object* v_msg_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1(v_msg_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
return v_res_2427_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2428_; double v___x_2429_; 
v___x_2428_ = lean_unsigned_to_nat(0u);
v___x_2429_ = lean_float_of_nat(v___x_2428_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg(lean_object* v_cls_2433_, lean_object* v_msg_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_){
_start:
{
lean_object* v_ref_2440_; lean_object* v___x_2441_; lean_object* v_a_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2487_; 
v_ref_2440_ = lean_ctor_get(v___y_2437_, 2);
v___x_2441_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0_spec__0(v_msg_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
v_a_2442_ = lean_ctor_get(v___x_2441_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2444_ = v___x_2441_;
v_isShared_2445_ = v_isSharedCheck_2487_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_a_2442_);
lean_dec(v___x_2441_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2487_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2446_; lean_object* v_traceState_2447_; lean_object* v_env_2448_; lean_object* v_nextMacroScope_2449_; lean_object* v_ngen_2450_; lean_object* v_auxDeclNGen_2451_; lean_object* v_cache_2452_; lean_object* v_recordedDeps_2453_; lean_object* v_messages_2454_; lean_object* v_infoState_2455_; lean_object* v_snapshotTasks_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2486_; 
v___x_2446_ = lean_st_ref_take(v___y_2438_);
v_traceState_2447_ = lean_ctor_get(v___x_2446_, 4);
v_env_2448_ = lean_ctor_get(v___x_2446_, 0);
v_nextMacroScope_2449_ = lean_ctor_get(v___x_2446_, 1);
v_ngen_2450_ = lean_ctor_get(v___x_2446_, 2);
v_auxDeclNGen_2451_ = lean_ctor_get(v___x_2446_, 3);
v_cache_2452_ = lean_ctor_get(v___x_2446_, 5);
v_recordedDeps_2453_ = lean_ctor_get(v___x_2446_, 6);
v_messages_2454_ = lean_ctor_get(v___x_2446_, 7);
v_infoState_2455_ = lean_ctor_get(v___x_2446_, 8);
v_snapshotTasks_2456_ = lean_ctor_get(v___x_2446_, 9);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2458_ = v___x_2446_;
v_isShared_2459_ = v_isSharedCheck_2486_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_snapshotTasks_2456_);
lean_inc(v_infoState_2455_);
lean_inc(v_messages_2454_);
lean_inc(v_recordedDeps_2453_);
lean_inc(v_cache_2452_);
lean_inc(v_traceState_2447_);
lean_inc(v_auxDeclNGen_2451_);
lean_inc(v_ngen_2450_);
lean_inc(v_nextMacroScope_2449_);
lean_inc(v_env_2448_);
lean_dec(v___x_2446_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2486_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
uint64_t v_tid_2460_; lean_object* v_traces_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2485_; 
v_tid_2460_ = lean_ctor_get_uint64(v_traceState_2447_, sizeof(void*)*1);
v_traces_2461_ = lean_ctor_get(v_traceState_2447_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v_traceState_2447_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2463_ = v_traceState_2447_;
v_isShared_2464_ = v_isSharedCheck_2485_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_traces_2461_);
lean_dec(v_traceState_2447_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2485_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; double v___x_2467_; uint8_t v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2476_; 
v___x_2465_ = lean_box(0);
v___x_2466_ = lean_box(0);
v___x_2467_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg___closed__0);
v___x_2468_ = 0;
v___x_2469_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg___closed__1));
v___x_2470_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2470_, 0, v_cls_2433_);
lean_ctor_set(v___x_2470_, 1, v___x_2466_);
lean_ctor_set(v___x_2470_, 2, v___x_2469_);
lean_ctor_set_float(v___x_2470_, sizeof(void*)*3, v___x_2467_);
lean_ctor_set_float(v___x_2470_, sizeof(void*)*3 + 8, v___x_2467_);
lean_ctor_set_uint8(v___x_2470_, sizeof(void*)*3 + 16, v___x_2468_);
v___x_2471_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg___closed__2));
v___x_2472_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2470_);
lean_ctor_set(v___x_2472_, 1, v_a_2442_);
lean_ctor_set(v___x_2472_, 2, v___x_2471_);
lean_inc(v_ref_2440_);
v___x_2473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2473_, 0, v_ref_2440_);
lean_ctor_set(v___x_2473_, 1, v___x_2472_);
v___x_2474_ = l_Lean_PersistentArray_push___redArg(v_traces_2461_, v___x_2473_);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 0, v___x_2474_);
v___x_2476_ = v___x_2463_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2474_);
lean_ctor_set_uint64(v_reuseFailAlloc_2484_, sizeof(void*)*1, v_tid_2460_);
v___x_2476_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
lean_object* v___x_2478_; 
if (v_isShared_2459_ == 0)
{
lean_ctor_set(v___x_2458_, 4, v___x_2476_);
v___x_2478_ = v___x_2458_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_env_2448_);
lean_ctor_set(v_reuseFailAlloc_2483_, 1, v_nextMacroScope_2449_);
lean_ctor_set(v_reuseFailAlloc_2483_, 2, v_ngen_2450_);
lean_ctor_set(v_reuseFailAlloc_2483_, 3, v_auxDeclNGen_2451_);
lean_ctor_set(v_reuseFailAlloc_2483_, 4, v___x_2476_);
lean_ctor_set(v_reuseFailAlloc_2483_, 5, v_cache_2452_);
lean_ctor_set(v_reuseFailAlloc_2483_, 6, v_recordedDeps_2453_);
lean_ctor_set(v_reuseFailAlloc_2483_, 7, v_messages_2454_);
lean_ctor_set(v_reuseFailAlloc_2483_, 8, v_infoState_2455_);
lean_ctor_set(v_reuseFailAlloc_2483_, 9, v_snapshotTasks_2456_);
v___x_2478_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
lean_object* v___x_2479_; lean_object* v___x_2481_; 
v___x_2479_ = lean_st_ref_put(v___y_2438_, v___x_2478_);
if (v_isShared_2445_ == 0)
{
lean_ctor_set(v___x_2444_, 0, v___x_2465_);
v___x_2481_ = v___x_2444_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v___x_2465_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg___boxed(lean_object* v_cls_2488_, lean_object* v_msg_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg(v_cls_2488_, v_msg_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
return v_res_2495_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__5(void){
_start:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2505_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__2));
v___x_2506_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__4));
v___x_2507_ = l_Lean_Name_append(v___x_2506_, v___x_2505_);
return v___x_2507_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__7(void){
_start:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2509_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__6));
v___x_2510_ = l_Lean_stringToMessageData(v___x_2509_);
return v___x_2510_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__9(void){
_start:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2512_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__8));
v___x_2513_ = l_Lean_stringToMessageData(v___x_2512_);
return v___x_2513_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__11(void){
_start:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2515_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__10));
v___x_2516_ = l_Lean_stringToMessageData(v___x_2515_);
return v___x_2516_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__15(void){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2520_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__14));
v___x_2521_ = lean_unsigned_to_nat(6u);
v___x_2522_ = lean_unsigned_to_nat(392u);
v___x_2523_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__13));
v___x_2524_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__12));
v___x_2525_ = l_mkPanicMessageWithDecl(v___x_2524_, v___x_2523_, v___x_2522_, v___x_2521_, v___x_2520_);
return v___x_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup(lean_object* v_e_2526_, lean_object* v_width_2527_, uint8_t v_synthetic_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_){
_start:
{
lean_object* v___y_2542_; lean_object* v___x_2563_; lean_object* v_atoms_2564_; lean_object* v___x_2565_; 
v___x_2563_ = lean_st_ref_get(v_a_2530_);
v_atoms_2564_ = lean_ctor_get(v___x_2563_, 0);
lean_inc_ref(v_atoms_2564_);
lean_dec(v___x_2563_);
v___x_2565_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_atoms_2564_, v_e_2526_);
lean_dec_ref(v_atoms_2564_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_toCold_2566_; lean_object* v_options_2567_; uint8_t v_hasTrace_2568_; 
v_toCold_2566_ = lean_ctor_get(v_a_2538_, 0);
v_options_2567_ = lean_ctor_get(v_toCold_2566_, 2);
v_hasTrace_2568_ = lean_ctor_get_uint8(v_options_2567_, sizeof(void*)*1);
if (v_hasTrace_2568_ == 0)
{
v___y_2542_ = v_a_2530_;
goto v___jp_2541_;
}
else
{
lean_object* v_inheritedTraceOptions_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; uint8_t v___x_2572_; 
v_inheritedTraceOptions_2569_ = lean_ctor_get(v_toCold_2566_, 11);
v___x_2570_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__2));
v___x_2571_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__5, &l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__5);
v___x_2572_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2569_, v_options_2567_, v___x_2571_);
if (v___x_2572_ == 0)
{
v___y_2542_ = v_a_2530_;
goto v___jp_2541_;
}
else
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___y_2581_; 
v___x_2573_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__7, &l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__7);
lean_inc(v_width_2527_);
v___x_2574_ = l_Nat_reprFast(v_width_2527_);
v___x_2575_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
v___x_2576_ = l_Lean_MessageData_ofFormat(v___x_2575_);
v___x_2577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2573_);
lean_ctor_set(v___x_2577_, 1, v___x_2576_);
v___x_2578_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__9, &l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__9);
v___x_2579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2577_);
lean_ctor_set(v___x_2579_, 1, v___x_2578_);
if (v_synthetic_2528_ == 0)
{
lean_object* v___x_2598_; 
v___x_2598_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__7));
v___y_2581_ = v___x_2598_;
goto v___jp_2580_;
}
else
{
lean_object* v___x_2599_; 
v___x_2599_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__10));
v___y_2581_ = v___x_2599_;
goto v___jp_2580_;
}
v___jp_2580_:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
lean_inc_ref(v___y_2581_);
v___x_2582_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2582_, 0, v___y_2581_);
v___x_2583_ = l_Lean_MessageData_ofFormat(v___x_2582_);
v___x_2584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2579_);
lean_ctor_set(v___x_2584_, 1, v___x_2583_);
v___x_2585_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__11, &l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__11);
v___x_2586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2584_);
lean_ctor_set(v___x_2586_, 1, v___x_2585_);
lean_inc_ref(v_e_2526_);
v___x_2587_ = l_Lean_MessageData_ofExpr(v_e_2526_);
v___x_2588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2586_);
lean_ctor_set(v___x_2588_, 1, v___x_2587_);
v___x_2589_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg(v___x_2570_, v___x_2588_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_);
if (lean_obj_tag(v___x_2589_) == 0)
{
lean_dec_ref_known(v___x_2589_, 1);
v___y_2542_ = v_a_2530_;
goto v___jp_2541_;
}
else
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
lean_dec(v_width_2527_);
lean_dec_ref(v_e_2526_);
v_a_2590_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2592_ = v___x_2589_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2589_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2595_; 
if (v_isShared_2593_ == 0)
{
v___x_2595_ = v___x_2592_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_a_2590_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
}
}
}
else
{
lean_object* v_val_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2628_; 
lean_dec_ref(v_e_2526_);
v_val_2600_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2602_ = v___x_2565_;
v_isShared_2603_ = v_isSharedCheck_2628_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_val_2600_);
lean_dec(v___x_2565_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2628_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v_width_2604_; lean_object* v_atomNumber_2605_; uint8_t v___x_2606_; 
v_width_2604_ = lean_ctor_get(v_val_2600_, 0);
lean_inc(v_width_2604_);
v_atomNumber_2605_ = lean_ctor_get(v_val_2600_, 1);
lean_inc(v_atomNumber_2605_);
lean_dec(v_val_2600_);
v___x_2606_ = lean_nat_dec_eq(v_width_2527_, v_width_2604_);
lean_dec(v_width_2604_);
lean_dec(v_width_2527_);
if (v___x_2606_ == 0)
{
lean_object* v___x_2607_; lean_object* v___x_2608_; 
lean_del_object(v___x_2602_);
v___x_2607_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__15, &l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__15);
v___x_2608_ = l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1(v___x_2607_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2615_ == 0)
{
lean_object* v_unused_2616_; 
v_unused_2616_ = lean_ctor_get(v___x_2608_, 0);
lean_dec(v_unused_2616_);
v___x_2610_ = v___x_2608_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_dec(v___x_2608_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 0, v_atomNumber_2605_);
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_atomNumber_2605_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_dec(v_atomNumber_2605_);
v_a_2617_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2608_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2608_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
else
{
lean_object* v___x_2626_; 
if (v_isShared_2603_ == 0)
{
lean_ctor_set_tag(v___x_2602_, 0);
lean_ctor_set(v___x_2602_, 0, v_atomNumber_2605_);
v___x_2626_ = v___x_2602_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_atomNumber_2605_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
v___jp_2541_:
{
lean_object* v___x_2543_; lean_object* v_atoms_2544_; lean_object* v_theoryState_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2559_; 
v___x_2543_ = lean_st_ref_take(v___y_2542_);
v_atoms_2544_ = lean_ctor_get(v___x_2543_, 0);
v_theoryState_2545_ = lean_ctor_get(v___x_2543_, 4);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2559_ == 0)
{
lean_object* v_unused_2560_; lean_object* v_unused_2561_; lean_object* v_unused_2562_; 
v_unused_2560_ = lean_ctor_get(v___x_2543_, 3);
lean_dec(v_unused_2560_);
v_unused_2561_ = lean_ctor_get(v___x_2543_, 2);
lean_dec(v_unused_2561_);
v_unused_2562_ = lean_ctor_get(v___x_2543_, 1);
lean_dec(v_unused_2562_);
v___x_2547_ = v___x_2543_;
v_isShared_2548_ = v_isSharedCheck_2559_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_theoryState_2545_);
lean_inc(v_atoms_2544_);
lean_dec(v___x_2543_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2559_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v_size_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2555_; 
v_size_2549_ = lean_ctor_get(v_atoms_2544_, 0);
lean_inc_n(v_size_2549_, 2);
v___x_2550_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2550_, 0, v_width_2527_);
lean_ctor_set(v___x_2550_, 1, v_size_2549_);
lean_ctor_set_uint8(v___x_2550_, sizeof(void*)*2, v_synthetic_2528_);
v___x_2551_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v_atoms_2544_, v_e_2526_, v___x_2550_);
v___x_2552_ = lean_box(0);
v___x_2553_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__1);
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 3, v___x_2553_);
lean_ctor_set(v___x_2547_, 2, v___x_2552_);
lean_ctor_set(v___x_2547_, 1, v___x_2552_);
lean_ctor_set(v___x_2547_, 0, v___x_2551_);
v___x_2555_ = v___x_2547_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v___x_2551_);
lean_ctor_set(v_reuseFailAlloc_2558_, 1, v___x_2552_);
lean_ctor_set(v_reuseFailAlloc_2558_, 2, v___x_2552_);
lean_ctor_set(v_reuseFailAlloc_2558_, 3, v___x_2553_);
lean_ctor_set(v_reuseFailAlloc_2558_, 4, v_theoryState_2545_);
v___x_2555_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2556_ = lean_st_ref_put(v___y_2542_, v___x_2555_);
v___x_2557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2557_, 0, v_size_2549_);
return v___x_2557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___boxed(lean_object* v_e_2629_, lean_object* v_width_2630_, lean_object* v_synthetic_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_){
_start:
{
uint8_t v_synthetic_boxed_2644_; lean_object* v_res_2645_; 
v_synthetic_boxed_2644_ = lean_unbox(v_synthetic_2631_);
v_res_2645_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup(v_e_2629_, v_width_2630_, v_synthetic_boxed_2644_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_);
lean_dec(v_a_2642_);
lean_dec_ref(v_a_2641_);
lean_dec(v_a_2640_);
lean_dec_ref(v_a_2639_);
lean_dec(v_a_2638_);
lean_dec_ref(v_a_2637_);
lean_dec(v_a_2636_);
lean_dec_ref(v_a_2635_);
lean_dec(v_a_2634_);
lean_dec(v_a_2633_);
lean_dec_ref(v_a_2632_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0(lean_object* v_cls_2646_, lean_object* v_msg_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v___x_2660_; 
v___x_2660_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg(v_cls_2646_, v_msg_2647_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___boxed(lean_object* v_cls_2661_, lean_object* v_msg_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v_res_2675_; 
v_res_2675_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0(v_cls_2661_, v_msg_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec(v___y_2671_);
lean_dec_ref(v___y_2670_);
lean_dec(v___y_2669_);
lean_dec_ref(v___y_2668_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
lean_dec(v___y_2665_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_modifyTheoryState___redArg(lean_object* v_f_2676_, lean_object* v_a_2677_){
_start:
{
lean_object* v___x_2679_; lean_object* v_atoms_2680_; lean_object* v_atomsAssignmentExprCache_2681_; lean_object* v_atomsAssignmentMapCache_2682_; lean_object* v_evalsAtCache_2683_; lean_object* v_theoryState_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2695_; 
v___x_2679_ = lean_st_ref_take(v_a_2677_);
v_atoms_2680_ = lean_ctor_get(v___x_2679_, 0);
v_atomsAssignmentExprCache_2681_ = lean_ctor_get(v___x_2679_, 1);
v_atomsAssignmentMapCache_2682_ = lean_ctor_get(v___x_2679_, 2);
v_evalsAtCache_2683_ = lean_ctor_get(v___x_2679_, 3);
v_theoryState_2684_ = lean_ctor_get(v___x_2679_, 4);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2686_ = v___x_2679_;
v_isShared_2687_ = v_isSharedCheck_2695_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_theoryState_2684_);
lean_inc(v_evalsAtCache_2683_);
lean_inc(v_atomsAssignmentMapCache_2682_);
lean_inc(v_atomsAssignmentExprCache_2681_);
lean_inc(v_atoms_2680_);
lean_dec(v___x_2679_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2695_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2691_; 
v___x_2688_ = lean_box(0);
v___x_2689_ = lean_apply_1(v_f_2676_, v_theoryState_2684_);
if (v_isShared_2687_ == 0)
{
lean_ctor_set(v___x_2686_, 4, v___x_2689_);
v___x_2691_ = v___x_2686_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v_atoms_2680_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v_atomsAssignmentExprCache_2681_);
lean_ctor_set(v_reuseFailAlloc_2694_, 2, v_atomsAssignmentMapCache_2682_);
lean_ctor_set(v_reuseFailAlloc_2694_, 3, v_evalsAtCache_2683_);
lean_ctor_set(v_reuseFailAlloc_2694_, 4, v___x_2689_);
v___x_2691_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2692_ = lean_st_ref_put(v_a_2677_, v___x_2691_);
v___x_2693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2688_);
return v___x_2693_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_modifyTheoryState___redArg___boxed(lean_object* v_f_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_modifyTheoryState___redArg(v_f_2696_, v_a_2697_);
lean_dec(v_a_2697_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_modifyTheoryState(lean_object* v_f_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_){
_start:
{
lean_object* v___x_2713_; lean_object* v_atoms_2714_; lean_object* v_atomsAssignmentExprCache_2715_; lean_object* v_atomsAssignmentMapCache_2716_; lean_object* v_evalsAtCache_2717_; lean_object* v_theoryState_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2729_; 
v___x_2713_ = lean_st_ref_take(v_a_2702_);
v_atoms_2714_ = lean_ctor_get(v___x_2713_, 0);
v_atomsAssignmentExprCache_2715_ = lean_ctor_get(v___x_2713_, 1);
v_atomsAssignmentMapCache_2716_ = lean_ctor_get(v___x_2713_, 2);
v_evalsAtCache_2717_ = lean_ctor_get(v___x_2713_, 3);
v_theoryState_2718_ = lean_ctor_get(v___x_2713_, 4);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2720_ = v___x_2713_;
v_isShared_2721_ = v_isSharedCheck_2729_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_theoryState_2718_);
lean_inc(v_evalsAtCache_2717_);
lean_inc(v_atomsAssignmentMapCache_2716_);
lean_inc(v_atomsAssignmentExprCache_2715_);
lean_inc(v_atoms_2714_);
lean_dec(v___x_2713_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2729_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2725_; 
v___x_2722_ = lean_box(0);
v___x_2723_ = lean_apply_1(v_f_2700_, v_theoryState_2718_);
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 4, v___x_2723_);
v___x_2725_ = v___x_2720_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_atoms_2714_);
lean_ctor_set(v_reuseFailAlloc_2728_, 1, v_atomsAssignmentExprCache_2715_);
lean_ctor_set(v_reuseFailAlloc_2728_, 2, v_atomsAssignmentMapCache_2716_);
lean_ctor_set(v_reuseFailAlloc_2728_, 3, v_evalsAtCache_2717_);
lean_ctor_set(v_reuseFailAlloc_2728_, 4, v___x_2723_);
v___x_2725_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2726_ = lean_st_ref_put(v_a_2702_, v___x_2725_);
v___x_2727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2722_);
return v___x_2727_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_modifyTheoryState___boxed(lean_object* v_f_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_modifyTheoryState(v_f_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_);
lean_dec(v_a_2741_);
lean_dec_ref(v_a_2740_);
lean_dec(v_a_2739_);
lean_dec_ref(v_a_2738_);
lean_dec(v_a_2737_);
lean_dec_ref(v_a_2736_);
lean_dec(v_a_2735_);
lean_dec_ref(v_a_2734_);
lean_dec(v_a_2733_);
lean_dec(v_a_2732_);
lean_dec_ref(v_a_2731_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyBinaryProof_x27(lean_object* v_mkFRefl_2744_, lean_object* v_fst_2745_, lean_object* v_fproof_2746_, lean_object* v_mkSRefl_2747_, lean_object* v_snd_2748_, lean_object* v_sproof_2749_){
_start:
{
if (lean_obj_tag(v_fproof_2746_) == 0)
{
lean_dec_ref(v_snd_2748_);
lean_dec_ref(v_mkSRefl_2747_);
if (lean_obj_tag(v_sproof_2749_) == 0)
{
lean_object* v___x_2750_; 
lean_dec_ref(v_fst_2745_);
lean_dec_ref(v_mkFRefl_2744_);
v___x_2750_ = lean_box(0);
return v___x_2750_;
}
else
{
lean_object* v_val_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2760_; 
v_val_2751_ = lean_ctor_get(v_sproof_2749_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v_sproof_2749_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2753_ = v_sproof_2749_;
v_isShared_2754_ = v_isSharedCheck_2760_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_val_2751_);
lean_dec(v_sproof_2749_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2760_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2758_; 
v___x_2755_ = lean_apply_1(v_mkFRefl_2744_, v_fst_2745_);
v___x_2756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2755_);
lean_ctor_set(v___x_2756_, 1, v_val_2751_);
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 0, v___x_2756_);
v___x_2758_ = v___x_2753_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v___x_2756_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
}
else
{
lean_dec_ref(v_fst_2745_);
lean_dec_ref(v_mkFRefl_2744_);
if (lean_obj_tag(v_sproof_2749_) == 0)
{
lean_object* v_val_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2770_; 
v_val_2761_ = lean_ctor_get(v_fproof_2746_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v_fproof_2746_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2763_ = v_fproof_2746_;
v_isShared_2764_ = v_isSharedCheck_2770_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_val_2761_);
lean_dec(v_fproof_2746_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2770_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2768_; 
v___x_2765_ = lean_apply_1(v_mkSRefl_2747_, v_snd_2748_);
v___x_2766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2766_, 0, v_val_2761_);
lean_ctor_set(v___x_2766_, 1, v___x_2765_);
if (v_isShared_2764_ == 0)
{
lean_ctor_set(v___x_2763_, 0, v___x_2766_);
v___x_2768_ = v___x_2763_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2766_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
else
{
lean_object* v_val_2771_; lean_object* v_val_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2780_; 
lean_dec_ref(v_snd_2748_);
lean_dec_ref(v_mkSRefl_2747_);
v_val_2771_ = lean_ctor_get(v_fproof_2746_, 0);
lean_inc(v_val_2771_);
lean_dec_ref_known(v_fproof_2746_, 1);
v_val_2772_ = lean_ctor_get(v_sproof_2749_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v_sproof_2749_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2774_ = v_sproof_2749_;
v_isShared_2775_ = v_isSharedCheck_2780_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_val_2772_);
lean_dec(v_sproof_2749_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2780_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2776_; lean_object* v___x_2778_; 
v___x_2776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2776_, 0, v_val_2771_);
lean_ctor_set(v___x_2776_, 1, v_val_2772_);
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 0, v___x_2776_);
v___x_2778_ = v___x_2774_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2776_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyBinaryProof(lean_object* v_mkRefl_2781_, lean_object* v_fst_2782_, lean_object* v_fproof_2783_, lean_object* v_snd_2784_, lean_object* v_sproof_2785_){
_start:
{
lean_object* v___x_2786_; 
lean_inc_ref(v_mkRefl_2781_);
v___x_2786_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyBinaryProof_x27(v_mkRefl_2781_, v_fst_2782_, v_fproof_2783_, v_mkRefl_2781_, v_snd_2784_, v_sproof_2785_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyTernaryProof(lean_object* v_mkRefl_2787_, lean_object* v_fst_2788_, lean_object* v_fproof_2789_, lean_object* v_snd_2790_, lean_object* v_sproof_2791_, lean_object* v_thd_2792_, lean_object* v_tproof_2793_){
_start:
{
if (lean_obj_tag(v_fproof_2789_) == 0)
{
lean_object* v___x_2794_; 
lean_inc_ref_n(v_mkRefl_2787_, 2);
v___x_2794_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyBinaryProof_x27(v_mkRefl_2787_, v_snd_2790_, v_sproof_2791_, v_mkRefl_2787_, v_thd_2792_, v_tproof_2793_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v___x_2795_; 
lean_dec_ref(v_fst_2788_);
lean_dec_ref(v_mkRefl_2787_);
v___x_2795_ = lean_box(0);
return v___x_2795_;
}
else
{
lean_object* v_val_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2805_; 
v_val_2796_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2798_ = v___x_2794_;
v_isShared_2799_ = v_isSharedCheck_2805_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_val_2796_);
lean_dec(v___x_2794_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2805_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2803_; 
v___x_2800_ = lean_apply_1(v_mkRefl_2787_, v_fst_2788_);
v___x_2801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2800_);
lean_ctor_set(v___x_2801_, 1, v_val_2796_);
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 0, v___x_2801_);
v___x_2803_ = v___x_2798_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2801_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
}
else
{
lean_object* v_val_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2827_; 
lean_dec_ref(v_fst_2788_);
v_val_2806_ = lean_ctor_get(v_fproof_2789_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v_fproof_2789_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2808_ = v_fproof_2789_;
v_isShared_2809_ = v_isSharedCheck_2827_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_val_2806_);
lean_dec(v_fproof_2789_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2827_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2810_; 
lean_inc_ref(v_thd_2792_);
lean_inc_ref(v_snd_2790_);
lean_inc_ref_n(v_mkRefl_2787_, 2);
v___x_2810_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyBinaryProof_x27(v_mkRefl_2787_, v_snd_2790_, v_sproof_2791_, v_mkRefl_2787_, v_thd_2792_, v_tproof_2793_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2816_; 
lean_inc_ref(v_mkRefl_2787_);
v___x_2811_ = lean_apply_1(v_mkRefl_2787_, v_snd_2790_);
v___x_2812_ = lean_apply_1(v_mkRefl_2787_, v_thd_2792_);
v___x_2813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2811_);
lean_ctor_set(v___x_2813_, 1, v___x_2812_);
v___x_2814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2814_, 0, v_val_2806_);
lean_ctor_set(v___x_2814_, 1, v___x_2813_);
if (v_isShared_2809_ == 0)
{
lean_ctor_set(v___x_2808_, 0, v___x_2814_);
v___x_2816_ = v___x_2808_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v___x_2814_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
else
{
lean_object* v_val_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2826_; 
lean_del_object(v___x_2808_);
lean_dec_ref(v_thd_2792_);
lean_dec_ref(v_snd_2790_);
lean_dec_ref(v_mkRefl_2787_);
v_val_2818_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2820_ = v___x_2810_;
v_isShared_2821_ = v_isSharedCheck_2826_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_val_2818_);
lean_dec(v___x_2810_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2826_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2822_; lean_object* v___x_2824_; 
v___x_2822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2822_, 0, v_val_2806_);
lean_ctor_set(v___x_2822_, 1, v_val_2818_);
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 0, v___x_2822_);
v___x_2824_ = v___x_2820_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v___x_2822_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_getHyps___redArg(lean_object* v_a_2828_){
_start:
{
lean_object* v_hypotheses_2830_; lean_object* v___x_2831_; 
v_hypotheses_2830_ = lean_ctor_get(v_a_2828_, 0);
lean_inc_ref(v_hypotheses_2830_);
v___x_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2831_, 0, v_hypotheses_2830_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_getHyps___redArg___boxed(lean_object* v_a_2832_, lean_object* v_a_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_getHyps___redArg(v_a_2832_);
lean_dec_ref(v_a_2832_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_getHyps(lean_object* v_a_2835_, lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_){
_start:
{
lean_object* v_hypotheses_2847_; lean_object* v___x_2848_; 
v_hypotheses_2847_ = lean_ctor_get(v_a_2835_, 0);
lean_inc_ref(v_hypotheses_2847_);
v___x_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2848_, 0, v_hypotheses_2847_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_getHyps___boxed(lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_getHyps(v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_);
lean_dec(v_a_2859_);
lean_dec_ref(v_a_2858_);
lean_dec(v_a_2857_);
lean_dec_ref(v_a_2856_);
lean_dec(v_a_2855_);
lean_dec_ref(v_a_2854_);
lean_dec(v_a_2853_);
lean_dec_ref(v_a_2852_);
lean_dec(v_a_2851_);
lean_dec(v_a_2850_);
lean_dec_ref(v_a_2849_);
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg(lean_object* v_m_2862_, lean_object* v_state_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_){
_start:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2876_ = lean_st_mk_ref(v_state_2863_);
lean_inc(v_a_2874_);
lean_inc_ref(v_a_2873_);
lean_inc(v_a_2872_);
lean_inc_ref(v_a_2871_);
lean_inc(v_a_2870_);
lean_inc_ref(v_a_2869_);
lean_inc(v_a_2868_);
lean_inc_ref(v_a_2867_);
lean_inc(v_a_2866_);
lean_inc(v_a_2865_);
lean_inc_ref(v_a_2864_);
lean_inc(v___x_2876_);
v___x_2877_ = lean_apply_13(v_m_2862_, v___x_2876_, v_a_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_, lean_box(0));
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_object* v_a_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2888_; 
v_a_2878_ = lean_ctor_get(v___x_2877_, 0);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2880_ = v___x_2877_;
v_isShared_2881_ = v_isSharedCheck_2888_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_dec(v___x_2877_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2888_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2882_; lean_object* v_lemmas_2883_; lean_object* v___x_2884_; lean_object* v___x_2886_; 
v___x_2882_ = lean_st_ref_get(v___x_2876_);
lean_dec(v___x_2876_);
v_lemmas_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc_ref(v_lemmas_2883_);
lean_dec(v___x_2882_);
v___x_2884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2884_, 0, v_a_2878_);
lean_ctor_set(v___x_2884_, 1, v_lemmas_2883_);
if (v_isShared_2881_ == 0)
{
lean_ctor_set(v___x_2880_, 0, v___x_2884_);
v___x_2886_ = v___x_2880_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v___x_2884_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
}
else
{
lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
lean_dec(v___x_2876_);
v_a_2889_ = lean_ctor_get(v___x_2877_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2891_ = v___x_2877_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2877_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2894_; 
if (v_isShared_2892_ == 0)
{
v___x_2894_ = v___x_2891_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_a_2889_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg___boxed(lean_object* v_m_2897_, lean_object* v_state_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_){
_start:
{
lean_object* v_res_2911_; 
v_res_2911_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg(v_m_2897_, v_state_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_);
lean_dec(v_a_2909_);
lean_dec_ref(v_a_2908_);
lean_dec(v_a_2907_);
lean_dec_ref(v_a_2906_);
lean_dec(v_a_2905_);
lean_dec_ref(v_a_2904_);
lean_dec(v_a_2903_);
lean_dec_ref(v_a_2902_);
lean_dec(v_a_2901_);
lean_dec(v_a_2900_);
lean_dec_ref(v_a_2899_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_run(lean_object* v_00_u03b1_2912_, lean_object* v_m_2913_, lean_object* v_state_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_, lean_object* v_a_2920_, lean_object* v_a_2921_, lean_object* v_a_2922_, lean_object* v_a_2923_, lean_object* v_a_2924_, lean_object* v_a_2925_){
_start:
{
lean_object* v___x_2927_; 
v___x_2927_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg(v_m_2913_, v_state_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, v_a_2920_, v_a_2921_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_);
return v___x_2927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_run___boxed(lean_object* v_00_u03b1_2928_, lean_object* v_m_2929_, lean_object* v_state_2930_, lean_object* v_a_2931_, lean_object* v_a_2932_, lean_object* v_a_2933_, lean_object* v_a_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_run(v_00_u03b1_2928_, v_m_2929_, v_state_2930_, v_a_2931_, v_a_2932_, v_a_2933_, v_a_2934_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_);
lean_dec(v_a_2941_);
lean_dec_ref(v_a_2940_);
lean_dec(v_a_2939_);
lean_dec_ref(v_a_2938_);
lean_dec(v_a_2937_);
lean_dec_ref(v_a_2936_);
lean_dec(v_a_2935_);
lean_dec_ref(v_a_2934_);
lean_dec(v_a_2933_);
lean_dec(v_a_2932_);
lean_dec_ref(v_a_2931_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg(lean_object* v_lemma_2944_, lean_object* v_a_2945_){
_start:
{
lean_object* v___x_2947_; lean_object* v_lemmas_2948_; lean_object* v_bvExprCache_2949_; lean_object* v_bvPredCache_2950_; lean_object* v_bvLogicalCache_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2962_; 
v___x_2947_ = lean_st_ref_take(v_a_2945_);
v_lemmas_2948_ = lean_ctor_get(v___x_2947_, 0);
v_bvExprCache_2949_ = lean_ctor_get(v___x_2947_, 1);
v_bvPredCache_2950_ = lean_ctor_get(v___x_2947_, 2);
v_bvLogicalCache_2951_ = lean_ctor_get(v___x_2947_, 3);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2953_ = v___x_2947_;
v_isShared_2954_ = v_isSharedCheck_2962_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_bvLogicalCache_2951_);
lean_inc(v_bvPredCache_2950_);
lean_inc(v_bvExprCache_2949_);
lean_inc(v_lemmas_2948_);
lean_dec(v___x_2947_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2962_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2958_; 
v___x_2955_ = lean_box(0);
v___x_2956_ = lean_array_push(v_lemmas_2948_, v_lemma_2944_);
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 0, v___x_2956_);
v___x_2958_ = v___x_2953_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v___x_2956_);
lean_ctor_set(v_reuseFailAlloc_2961_, 1, v_bvExprCache_2949_);
lean_ctor_set(v_reuseFailAlloc_2961_, 2, v_bvPredCache_2950_);
lean_ctor_set(v_reuseFailAlloc_2961_, 3, v_bvLogicalCache_2951_);
v___x_2958_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2959_ = lean_st_ref_put(v_a_2945_, v___x_2958_);
v___x_2960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2955_);
return v___x_2960_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg___boxed(lean_object* v_lemma_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_){
_start:
{
lean_object* v_res_2966_; 
v_res_2966_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg(v_lemma_2963_, v_a_2964_);
lean_dec(v_a_2964_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma(lean_object* v_lemma_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_, lean_object* v_a_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_){
_start:
{
lean_object* v___x_2981_; 
v___x_2981_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg(v_lemma_2967_, v_a_2968_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___boxed(lean_object* v_lemma_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma(v_lemma_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_);
lean_dec(v_a_2994_);
lean_dec_ref(v_a_2993_);
lean_dec(v_a_2992_);
lean_dec_ref(v_a_2991_);
lean_dec(v_a_2990_);
lean_dec_ref(v_a_2989_);
lean_dec(v_a_2988_);
lean_dec_ref(v_a_2987_);
lean_dec(v_a_2986_);
lean_dec(v_a_2985_);
lean_dec_ref(v_a_2984_);
lean_dec(v_a_2983_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas___redArg(lean_object* v_a_2999_){
_start:
{
lean_object* v___x_3001_; lean_object* v_bvExprCache_3002_; lean_object* v_bvPredCache_3003_; lean_object* v_bvLogicalCache_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3015_; 
v___x_3001_ = lean_st_ref_take(v_a_2999_);
v_bvExprCache_3002_ = lean_ctor_get(v___x_3001_, 1);
v_bvPredCache_3003_ = lean_ctor_get(v___x_3001_, 2);
v_bvLogicalCache_3004_ = lean_ctor_get(v___x_3001_, 3);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3015_ == 0)
{
lean_object* v_unused_3016_; 
v_unused_3016_ = lean_ctor_get(v___x_3001_, 0);
lean_dec(v_unused_3016_);
v___x_3006_ = v___x_3001_;
v_isShared_3007_ = v_isSharedCheck_3015_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_bvLogicalCache_3004_);
lean_inc(v_bvPredCache_3003_);
lean_inc(v_bvExprCache_3002_);
lean_dec(v___x_3001_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3015_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3011_; 
v___x_3008_ = lean_box(0);
v___x_3009_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas___redArg___closed__0));
if (v_isShared_3007_ == 0)
{
lean_ctor_set(v___x_3006_, 0, v___x_3009_);
v___x_3011_ = v___x_3006_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v___x_3009_);
lean_ctor_set(v_reuseFailAlloc_3014_, 1, v_bvExprCache_3002_);
lean_ctor_set(v_reuseFailAlloc_3014_, 2, v_bvPredCache_3003_);
lean_ctor_set(v_reuseFailAlloc_3014_, 3, v_bvLogicalCache_3004_);
v___x_3011_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___x_3012_ = lean_st_ref_put(v_a_2999_, v___x_3011_);
v___x_3013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3008_);
return v___x_3013_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas___redArg___boxed(lean_object* v_a_3017_, lean_object* v_a_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas___redArg(v_a_3017_);
lean_dec(v_a_3017_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas(lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_){
_start:
{
lean_object* v___x_3033_; 
v___x_3033_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas___redArg(v_a_3020_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas___boxed(lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_){
_start:
{
lean_object* v_res_3047_; 
v_res_3047_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas(v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_);
lean_dec(v_a_3045_);
lean_dec_ref(v_a_3044_);
lean_dec(v_a_3043_);
lean_dec_ref(v_a_3042_);
lean_dec(v_a_3041_);
lean_dec_ref(v_a_3040_);
lean_dec(v_a_3039_);
lean_dec_ref(v_a_3038_);
lean_dec(v_a_3037_);
lean_dec(v_a_3036_);
lean_dec_ref(v_a_3035_);
lean_dec(v_a_3034_);
return v_res_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_getLemmas___redArg(lean_object* v_a_3048_){
_start:
{
lean_object* v___x_3050_; lean_object* v_lemmas_3051_; lean_object* v___x_3052_; 
v___x_3050_ = lean_st_ref_get(v_a_3048_);
v_lemmas_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc_ref(v_lemmas_3051_);
lean_dec(v___x_3050_);
v___x_3052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3052_, 0, v_lemmas_3051_);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_getLemmas___redArg___boxed(lean_object* v_a_3053_, lean_object* v_a_3054_){
_start:
{
lean_object* v_res_3055_; 
v_res_3055_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_getLemmas___redArg(v_a_3053_);
lean_dec(v_a_3053_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_getLemmas(lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_){
_start:
{
lean_object* v___x_3069_; 
v___x_3069_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_getLemmas___redArg(v_a_3056_);
return v___x_3069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_getLemmas___boxed(lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_){
_start:
{
lean_object* v_res_3083_; 
v_res_3083_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_getLemmas(v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_);
lean_dec(v_a_3081_);
lean_dec_ref(v_a_3080_);
lean_dec(v_a_3079_);
lean_dec_ref(v_a_3078_);
lean_dec(v_a_3077_);
lean_dec_ref(v_a_3076_);
lean_dec(v_a_3075_);
lean_dec_ref(v_a_3074_);
lean_dec(v_a_3073_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
lean_dec(v_a_3070_);
return v_res_3083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache(lean_object* v_e_3086_, lean_object* v_f_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_){
_start:
{
lean_object* v___f_3101_; lean_object* v___f_3102_; lean_object* v___x_3103_; lean_object* v_bvExprCache_3104_; lean_object* v___x_3105_; 
v___f_3101_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__0));
v___f_3102_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__1));
v___x_3103_ = lean_st_ref_get(v_a_3088_);
v_bvExprCache_3104_ = lean_ctor_get(v___x_3103_, 1);
lean_inc_ref(v_bvExprCache_3104_);
lean_dec(v___x_3103_);
lean_inc_ref(v_e_3086_);
v___x_3105_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_3101_, v___f_3102_, v_bvExprCache_3104_, v_e_3086_);
lean_dec_ref(v_bvExprCache_3104_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v___x_3106_; 
lean_inc(v_a_3099_);
lean_inc_ref(v_a_3098_);
lean_inc(v_a_3097_);
lean_inc_ref(v_a_3096_);
lean_inc(v_a_3095_);
lean_inc_ref(v_a_3094_);
lean_inc(v_a_3093_);
lean_inc_ref(v_a_3092_);
lean_inc(v_a_3091_);
lean_inc(v_a_3090_);
lean_inc_ref(v_a_3089_);
lean_inc(v_a_3088_);
lean_inc_ref(v_e_3086_);
v___x_3106_ = lean_apply_14(v_f_3087_, v_e_3086_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, lean_box(0));
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3128_; 
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3109_ = v___x_3106_;
v_isShared_3110_ = v_isSharedCheck_3128_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3106_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3128_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3111_; lean_object* v_lemmas_3112_; lean_object* v_bvExprCache_3113_; lean_object* v_bvPredCache_3114_; lean_object* v_bvLogicalCache_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3127_; 
v___x_3111_ = lean_st_ref_take(v_a_3088_);
v_lemmas_3112_ = lean_ctor_get(v___x_3111_, 0);
v_bvExprCache_3113_ = lean_ctor_get(v___x_3111_, 1);
v_bvPredCache_3114_ = lean_ctor_get(v___x_3111_, 2);
v_bvLogicalCache_3115_ = lean_ctor_get(v___x_3111_, 3);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3117_ = v___x_3111_;
v_isShared_3118_ = v_isSharedCheck_3127_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_bvLogicalCache_3115_);
lean_inc(v_bvPredCache_3114_);
lean_inc(v_bvExprCache_3113_);
lean_inc(v_lemmas_3112_);
lean_dec(v___x_3111_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3127_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3119_; lean_object* v___x_3121_; 
lean_inc(v_a_3107_);
v___x_3119_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_3101_, v___f_3102_, v_bvExprCache_3113_, v_e_3086_, v_a_3107_);
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 1, v___x_3119_);
v___x_3121_ = v___x_3117_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_lemmas_3112_);
lean_ctor_set(v_reuseFailAlloc_3126_, 1, v___x_3119_);
lean_ctor_set(v_reuseFailAlloc_3126_, 2, v_bvPredCache_3114_);
lean_ctor_set(v_reuseFailAlloc_3126_, 3, v_bvLogicalCache_3115_);
v___x_3121_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
lean_object* v___x_3122_; lean_object* v___x_3124_; 
v___x_3122_ = lean_st_ref_put(v_a_3088_, v___x_3121_);
if (v_isShared_3110_ == 0)
{
v___x_3124_ = v___x_3109_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3107_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3086_);
return v___x_3106_;
}
}
else
{
lean_object* v_val_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
lean_dec_ref(v_f_3087_);
lean_dec_ref(v_e_3086_);
v_val_3129_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___x_3105_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_val_3129_);
lean_dec(v___x_3105_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
lean_ctor_set_tag(v___x_3131_, 0);
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_val_3129_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___boxed(lean_object* v_e_3137_, lean_object* v_f_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_){
_start:
{
lean_object* v_res_3152_; 
v_res_3152_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache(v_e_3137_, v_f_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_);
lean_dec(v_a_3150_);
lean_dec_ref(v_a_3149_);
lean_dec(v_a_3148_);
lean_dec_ref(v_a_3147_);
lean_dec(v_a_3146_);
lean_dec_ref(v_a_3145_);
lean_dec(v_a_3144_);
lean_dec_ref(v_a_3143_);
lean_dec(v_a_3142_);
lean_dec(v_a_3141_);
lean_dec_ref(v_a_3140_);
lean_dec(v_a_3139_);
return v_res_3152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache(lean_object* v_e_3153_, lean_object* v_f_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_){
_start:
{
lean_object* v___f_3168_; lean_object* v___f_3169_; lean_object* v___x_3170_; lean_object* v_bvPredCache_3171_; lean_object* v___x_3172_; 
v___f_3168_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__0));
v___f_3169_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__1));
v___x_3170_ = lean_st_ref_get(v_a_3155_);
v_bvPredCache_3171_ = lean_ctor_get(v___x_3170_, 2);
lean_inc_ref(v_bvPredCache_3171_);
lean_dec(v___x_3170_);
lean_inc_ref(v_e_3153_);
v___x_3172_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_3168_, v___f_3169_, v_bvPredCache_3171_, v_e_3153_);
lean_dec_ref(v_bvPredCache_3171_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_object* v___x_3173_; 
lean_inc(v_a_3166_);
lean_inc_ref(v_a_3165_);
lean_inc(v_a_3164_);
lean_inc_ref(v_a_3163_);
lean_inc(v_a_3162_);
lean_inc_ref(v_a_3161_);
lean_inc(v_a_3160_);
lean_inc_ref(v_a_3159_);
lean_inc(v_a_3158_);
lean_inc(v_a_3157_);
lean_inc_ref(v_a_3156_);
lean_inc(v_a_3155_);
lean_inc_ref(v_e_3153_);
v___x_3173_ = lean_apply_14(v_f_3154_, v_e_3153_, v_a_3155_, v_a_3156_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_, v_a_3161_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_, lean_box(0));
if (lean_obj_tag(v___x_3173_) == 0)
{
lean_object* v_a_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3195_; 
v_a_3174_ = lean_ctor_get(v___x_3173_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3176_ = v___x_3173_;
v_isShared_3177_ = v_isSharedCheck_3195_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_a_3174_);
lean_dec(v___x_3173_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3195_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3178_; lean_object* v_lemmas_3179_; lean_object* v_bvExprCache_3180_; lean_object* v_bvPredCache_3181_; lean_object* v_bvLogicalCache_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3194_; 
v___x_3178_ = lean_st_ref_take(v_a_3155_);
v_lemmas_3179_ = lean_ctor_get(v___x_3178_, 0);
v_bvExprCache_3180_ = lean_ctor_get(v___x_3178_, 1);
v_bvPredCache_3181_ = lean_ctor_get(v___x_3178_, 2);
v_bvLogicalCache_3182_ = lean_ctor_get(v___x_3178_, 3);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3184_ = v___x_3178_;
v_isShared_3185_ = v_isSharedCheck_3194_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_bvLogicalCache_3182_);
lean_inc(v_bvPredCache_3181_);
lean_inc(v_bvExprCache_3180_);
lean_inc(v_lemmas_3179_);
lean_dec(v___x_3178_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3194_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3186_; lean_object* v___x_3188_; 
lean_inc(v_a_3174_);
v___x_3186_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_3168_, v___f_3169_, v_bvPredCache_3181_, v_e_3153_, v_a_3174_);
if (v_isShared_3185_ == 0)
{
lean_ctor_set(v___x_3184_, 2, v___x_3186_);
v___x_3188_ = v___x_3184_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_lemmas_3179_);
lean_ctor_set(v_reuseFailAlloc_3193_, 1, v_bvExprCache_3180_);
lean_ctor_set(v_reuseFailAlloc_3193_, 2, v___x_3186_);
lean_ctor_set(v_reuseFailAlloc_3193_, 3, v_bvLogicalCache_3182_);
v___x_3188_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
lean_object* v___x_3189_; lean_object* v___x_3191_; 
v___x_3189_ = lean_st_ref_put(v_a_3155_, v___x_3188_);
if (v_isShared_3177_ == 0)
{
v___x_3191_ = v___x_3176_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_a_3174_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3153_);
return v___x_3173_;
}
}
else
{
lean_object* v_val_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3203_; 
lean_dec_ref(v_f_3154_);
lean_dec_ref(v_e_3153_);
v_val_3196_ = lean_ctor_get(v___x_3172_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3198_ = v___x_3172_;
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_val_3196_);
lean_dec(v___x_3172_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3201_; 
if (v_isShared_3199_ == 0)
{
lean_ctor_set_tag(v___x_3198_, 0);
v___x_3201_ = v___x_3198_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_val_3196_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache___boxed(lean_object* v_e_3204_, lean_object* v_f_3205_, lean_object* v_a_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_){
_start:
{
lean_object* v_res_3219_; 
v_res_3219_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache(v_e_3204_, v_f_3205_, v_a_3206_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_);
lean_dec(v_a_3217_);
lean_dec_ref(v_a_3216_);
lean_dec(v_a_3215_);
lean_dec_ref(v_a_3214_);
lean_dec(v_a_3213_);
lean_dec_ref(v_a_3212_);
lean_dec(v_a_3211_);
lean_dec_ref(v_a_3210_);
lean_dec(v_a_3209_);
lean_dec(v_a_3208_);
lean_dec_ref(v_a_3207_);
lean_dec(v_a_3206_);
return v_res_3219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache(lean_object* v_e_3220_, lean_object* v_f_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_){
_start:
{
lean_object* v___f_3235_; lean_object* v___f_3236_; lean_object* v___x_3237_; lean_object* v_bvLogicalCache_3238_; lean_object* v___x_3239_; 
v___f_3235_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__0));
v___f_3236_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__1));
v___x_3237_ = lean_st_ref_get(v_a_3222_);
v_bvLogicalCache_3238_ = lean_ctor_get(v___x_3237_, 3);
lean_inc_ref(v_bvLogicalCache_3238_);
lean_dec(v___x_3237_);
lean_inc_ref(v_e_3220_);
v___x_3239_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_3235_, v___f_3236_, v_bvLogicalCache_3238_, v_e_3220_);
lean_dec_ref(v_bvLogicalCache_3238_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v___x_3240_; 
lean_inc(v_a_3233_);
lean_inc_ref(v_a_3232_);
lean_inc(v_a_3231_);
lean_inc_ref(v_a_3230_);
lean_inc(v_a_3229_);
lean_inc_ref(v_a_3228_);
lean_inc(v_a_3227_);
lean_inc_ref(v_a_3226_);
lean_inc(v_a_3225_);
lean_inc(v_a_3224_);
lean_inc_ref(v_a_3223_);
lean_inc(v_a_3222_);
lean_inc_ref(v_e_3220_);
v___x_3240_ = lean_apply_14(v_f_3221_, v_e_3220_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, lean_box(0));
if (lean_obj_tag(v___x_3240_) == 0)
{
lean_object* v_a_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3262_; 
v_a_3241_ = lean_ctor_get(v___x_3240_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3243_ = v___x_3240_;
v_isShared_3244_ = v_isSharedCheck_3262_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_a_3241_);
lean_dec(v___x_3240_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3262_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v___x_3245_; lean_object* v_lemmas_3246_; lean_object* v_bvExprCache_3247_; lean_object* v_bvPredCache_3248_; lean_object* v_bvLogicalCache_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3261_; 
v___x_3245_ = lean_st_ref_take(v_a_3222_);
v_lemmas_3246_ = lean_ctor_get(v___x_3245_, 0);
v_bvExprCache_3247_ = lean_ctor_get(v___x_3245_, 1);
v_bvPredCache_3248_ = lean_ctor_get(v___x_3245_, 2);
v_bvLogicalCache_3249_ = lean_ctor_get(v___x_3245_, 3);
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3261_ == 0)
{
v___x_3251_ = v___x_3245_;
v_isShared_3252_ = v_isSharedCheck_3261_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_bvLogicalCache_3249_);
lean_inc(v_bvPredCache_3248_);
lean_inc(v_bvExprCache_3247_);
lean_inc(v_lemmas_3246_);
lean_dec(v___x_3245_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3261_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3253_; lean_object* v___x_3255_; 
lean_inc(v_a_3241_);
v___x_3253_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_3235_, v___f_3236_, v_bvLogicalCache_3249_, v_e_3220_, v_a_3241_);
if (v_isShared_3252_ == 0)
{
lean_ctor_set(v___x_3251_, 3, v___x_3253_);
v___x_3255_ = v___x_3251_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3260_; 
v_reuseFailAlloc_3260_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3260_, 0, v_lemmas_3246_);
lean_ctor_set(v_reuseFailAlloc_3260_, 1, v_bvExprCache_3247_);
lean_ctor_set(v_reuseFailAlloc_3260_, 2, v_bvPredCache_3248_);
lean_ctor_set(v_reuseFailAlloc_3260_, 3, v___x_3253_);
v___x_3255_ = v_reuseFailAlloc_3260_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
lean_object* v___x_3256_; lean_object* v___x_3258_; 
v___x_3256_ = lean_st_ref_put(v_a_3222_, v___x_3255_);
if (v_isShared_3244_ == 0)
{
v___x_3258_ = v___x_3243_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_a_3241_);
v___x_3258_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
return v___x_3258_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3220_);
return v___x_3240_;
}
}
else
{
lean_object* v_val_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3270_; 
lean_dec_ref(v_f_3221_);
lean_dec_ref(v_e_3220_);
v_val_3263_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3265_ = v___x_3239_;
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_val_3263_);
lean_dec(v___x_3239_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v___x_3268_; 
if (v_isShared_3266_ == 0)
{
lean_ctor_set_tag(v___x_3265_, 0);
v___x_3268_ = v___x_3265_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v_val_3263_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___boxed(lean_object* v_e_3271_, lean_object* v_f_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache(v_e_3271_, v_f_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_);
lean_dec(v_a_3284_);
lean_dec_ref(v_a_3283_);
lean_dec(v_a_3282_);
lean_dec_ref(v_a_3281_);
lean_dec(v_a_3280_);
lean_dec_ref(v_a_3279_);
lean_dec(v_a_3278_);
lean_dec_ref(v_a_3277_);
lean_dec(v_a_3276_);
lean_dec(v_a_3275_);
lean_dec_ref(v_a_3274_);
lean_dec(v_a_3273_);
return v_res_3286_;
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
