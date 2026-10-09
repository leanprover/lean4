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
lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0(uint8_t v_x_75_){
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
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_75_ = stack[0].m_num;
lean_object* v_res_83_;
v_res_83_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0(v_x_75_);
stack->m_obj
 = v_res_83_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___boxed(lean_object* v_x_84_){
_start:
{
uint8_t v_x_boxed_85_; lean_object* v_res_86_; 
v_x_boxed_85_ = lean_unbox(v_x_84_);
v_res_86_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0(v_x_boxed_85_);
return v_res_86_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__2(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = lean_box(0);
v___x_94_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__1));
v___x_95_ = l_Lean_mkConst(v___x_94_, v___x_93_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__3(void){
_start:
{
lean_object* v___x_96_; lean_object* v___f_97_; lean_object* v___x_98_; 
v___x_96_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__2, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__2);
v___f_97_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__0));
v___x_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_98_, 0, v___f_97_);
lean_ctor_set(v___x_98_, 1, v___x_96_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp(void){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__3, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___closed__3);
return v___x_99_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__3(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_108_ = lean_box(0);
v___x_109_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__2));
v___x_110_ = l_Lean_mkConst(v___x_109_, v___x_108_);
return v___x_110_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__6(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_118_ = lean_box(0);
v___x_119_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__5));
v___x_120_ = l_Lean_mkConst(v___x_119_, v___x_118_);
return v___x_120_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__9(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_128_ = lean_box(0);
v___x_129_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__8));
v___x_130_ = l_Lean_mkConst(v___x_129_, v___x_128_);
return v___x_130_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__12(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_138_ = lean_box(0);
v___x_139_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__11));
v___x_140_ = l_Lean_mkConst(v___x_139_, v___x_138_);
return v___x_140_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__15(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_box(0);
v___x_149_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__14));
v___x_150_ = l_Lean_mkConst(v___x_149_, v___x_148_);
return v___x_150_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__18(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_box(0);
v___x_159_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__17));
v___x_160_ = l_Lean_mkConst(v___x_159_, v___x_158_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__21(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = lean_box(0);
v___x_169_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__20));
v___x_170_ = l_Lean_mkConst(v___x_169_, v___x_168_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0(lean_object* v_x_171_){
_start:
{
switch(lean_obj_tag(v_x_171_))
{
case 0:
{
lean_object* v___x_172_; 
v___x_172_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__3, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__3);
return v___x_172_;
}
case 1:
{
lean_object* v_n_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v_n_173_ = lean_ctor_get(v_x_171_, 0);
lean_inc(v_n_173_);
lean_dec_ref_known(v_x_171_, 1);
v___x_174_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__6, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__6);
v___x_175_ = l_Lean_mkNatLit(v_n_173_);
v___x_176_ = l_Lean_Expr_app___override(v___x_174_, v___x_175_);
return v___x_176_;
}
case 2:
{
lean_object* v_n_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_n_177_ = lean_ctor_get(v_x_171_, 0);
lean_inc(v_n_177_);
lean_dec_ref_known(v_x_171_, 1);
v___x_178_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__9, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__9);
v___x_179_ = l_Lean_mkNatLit(v_n_177_);
v___x_180_ = l_Lean_Expr_app___override(v___x_178_, v___x_179_);
return v___x_180_;
}
case 3:
{
lean_object* v_n_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v_n_181_ = lean_ctor_get(v_x_171_, 0);
lean_inc(v_n_181_);
lean_dec_ref_known(v_x_171_, 1);
v___x_182_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__12, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__12);
v___x_183_ = l_Lean_mkNatLit(v_n_181_);
v___x_184_ = l_Lean_Expr_app___override(v___x_182_, v___x_183_);
return v___x_184_;
}
case 4:
{
lean_object* v___x_185_; 
v___x_185_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__15, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__15);
return v___x_185_;
}
case 5:
{
lean_object* v___x_186_; 
v___x_186_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__18, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__18_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__18);
return v___x_186_;
}
default: 
{
lean_object* v___x_187_; 
v___x_187_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__21, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__21);
return v___x_187_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__2(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_194_ = lean_box(0);
v___x_195_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__1));
v___x_196_ = l_Lean_mkConst(v___x_195_, v___x_194_);
return v___x_196_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__3(void){
_start:
{
lean_object* v___x_197_; lean_object* v___f_198_; lean_object* v___x_199_; 
v___x_197_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__2, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__2);
v___f_198_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__0));
v___x_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_199_, 0, v___f_198_);
lean_ctor_set(v___x_199_, 1, v___x_197_);
return v___x_199_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp(void){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__3, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___closed__3);
return v___x_200_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__3(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_209_ = lean_box(0);
v___x_210_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__2));
v___x_211_ = l_Lean_mkConst(v___x_210_, v___x_209_);
return v___x_211_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__6(void){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_219_ = lean_box(0);
v___x_220_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__5));
v___x_221_ = l_Lean_mkConst(v___x_220_, v___x_219_);
return v___x_221_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__10(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_227_ = lean_box(0);
v___x_228_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__9));
v___x_229_ = l_Lean_Expr_const___override(v___x_228_, v___x_227_);
return v___x_229_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__13(void){
_start:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_237_ = lean_box(0);
v___x_238_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__12));
v___x_239_ = l_Lean_mkConst(v___x_238_, v___x_237_);
return v___x_239_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__16(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_247_ = lean_box(0);
v___x_248_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__15));
v___x_249_ = l_Lean_mkConst(v___x_248_, v___x_247_);
return v___x_249_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__19(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = lean_box(0);
v___x_258_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__18));
v___x_259_ = l_Lean_mkConst(v___x_258_, v___x_257_);
return v___x_259_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__23(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_unsigned_to_nat(1u);
v___x_266_ = l_Lean_Level_ofNat(v___x_265_);
return v___x_266_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__24(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_267_ = lean_box(0);
v___x_268_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__23, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__23_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__23);
v___x_269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v___x_267_);
return v___x_269_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__25(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_270_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__24, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__24_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__24);
v___x_271_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__22));
v___x_272_ = l_Lean_mkConst(v___x_271_, v___x_270_);
return v___x_272_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__28(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_276_ = lean_box(0);
v___x_277_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__27));
v___x_278_ = l_Lean_mkConst(v___x_277_, v___x_276_);
return v___x_278_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__31(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_286_ = lean_box(0);
v___x_287_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__30));
v___x_288_ = l_Lean_mkConst(v___x_287_, v___x_286_);
return v___x_288_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__34(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = lean_box(0);
v___x_297_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__33));
v___x_298_ = l_Lean_mkConst(v___x_297_, v___x_296_);
return v___x_298_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__37(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_306_ = lean_box(0);
v___x_307_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__36));
v___x_308_ = l_Lean_mkConst(v___x_307_, v___x_306_);
return v___x_308_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__40(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_316_ = lean_box(0);
v___x_317_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__39));
v___x_318_ = l_Lean_mkConst(v___x_317_, v___x_316_);
return v___x_318_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__43(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_326_ = lean_box(0);
v___x_327_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__42));
v___x_328_ = l_Lean_mkConst(v___x_327_, v___x_326_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(lean_object* v_w_329_, lean_object* v_a_330_){
_start:
{
switch(lean_obj_tag(v_a_330_))
{
case 0:
{
lean_object* v_idx_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v_idx_331_ = lean_ctor_get(v_a_330_, 1);
lean_inc(v_idx_331_);
lean_dec_ref_known(v_a_330_, 2);
v___x_332_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__3, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__3);
v___x_333_ = l_Lean_mkNatLit(v_w_329_);
v___x_334_ = l_Lean_mkNatLit(v_idx_331_);
v___x_335_ = l_Lean_mkAppB(v___x_332_, v___x_333_, v___x_334_);
return v___x_335_;
}
case 1:
{
lean_object* v_val_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v_val_336_ = lean_ctor_get(v_a_330_, 1);
lean_inc(v_val_336_);
lean_dec_ref_known(v_a_330_, 2);
v___x_337_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__6, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__6);
v___x_338_ = l_Lean_mkNatLit(v_w_329_);
v___x_339_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__10, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__10_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__10);
v___x_340_ = l_Lean_mkNatLit(v_val_336_);
lean_inc_ref(v___x_338_);
v___x_341_ = l_Lean_mkAppB(v___x_339_, v___x_338_, v___x_340_);
v___x_342_ = l_Lean_mkAppB(v___x_337_, v___x_338_, v___x_341_);
return v___x_342_;
}
case 2:
{
lean_object* v_w_343_; lean_object* v_start_344_; lean_object* v_expr_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v_w_343_ = lean_ctor_get(v_a_330_, 0);
lean_inc_n(v_w_343_, 2);
v_start_344_ = lean_ctor_get(v_a_330_, 1);
lean_inc(v_start_344_);
v_expr_345_ = lean_ctor_get(v_a_330_, 3);
lean_inc_ref(v_expr_345_);
lean_dec_ref_known(v_a_330_, 4);
v___x_346_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__13, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__13_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__13);
v___x_347_ = l_Lean_mkNatLit(v_w_343_);
v___x_348_ = l_Lean_mkNatLit(v_start_344_);
v___x_349_ = l_Lean_mkNatLit(v_w_329_);
v___x_350_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_343_, v_expr_345_);
v___x_351_ = l_Lean_mkApp4(v___x_346_, v___x_347_, v___x_348_, v___x_349_, v___x_350_);
return v___x_351_;
}
case 3:
{
lean_object* v_lhs_352_; uint8_t v_op_353_; lean_object* v_rhs_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___y_359_; 
v_lhs_352_ = lean_ctor_get(v_a_330_, 1);
lean_inc_ref(v_lhs_352_);
v_op_353_ = lean_ctor_get_uint8(v_a_330_, sizeof(void*)*3 + 8);
v_rhs_354_ = lean_ctor_get(v_a_330_, 2);
lean_inc_ref(v_rhs_354_);
lean_dec_ref_known(v_a_330_, 3);
v___x_355_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__16, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__16_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__16);
lean_inc_n(v_w_329_, 2);
v___x_356_ = l_Lean_mkNatLit(v_w_329_);
v___x_357_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_329_, v_lhs_352_);
switch(v_op_353_)
{
case 0:
{
lean_object* v___x_362_; 
v___x_362_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__6, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__6);
v___y_359_ = v___x_362_;
goto v___jp_358_;
}
case 1:
{
lean_object* v___x_363_; 
v___x_363_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__9, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__9);
v___y_359_ = v___x_363_;
goto v___jp_358_;
}
case 2:
{
lean_object* v___x_364_; 
v___x_364_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__12, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__12);
v___y_359_ = v___x_364_;
goto v___jp_358_;
}
case 3:
{
lean_object* v___x_365_; 
v___x_365_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__15, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__15);
v___y_359_ = v___x_365_;
goto v___jp_358_;
}
case 4:
{
lean_object* v___x_366_; 
v___x_366_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__18, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__18_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__18);
v___y_359_ = v___x_366_;
goto v___jp_358_;
}
case 5:
{
lean_object* v___x_367_; 
v___x_367_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__21, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__21);
v___y_359_ = v___x_367_;
goto v___jp_358_;
}
default: 
{
lean_object* v___x_368_; 
v___x_368_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__24, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__24_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinOp___lam__0___closed__24);
v___y_359_ = v___x_368_;
goto v___jp_358_;
}
}
v___jp_358_:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_329_, v_rhs_354_);
lean_inc_ref(v___y_359_);
v___x_361_ = l_Lean_mkApp4(v___x_355_, v___x_356_, v___x_357_, v___y_359_, v___x_360_);
return v___x_361_;
}
}
case 4:
{
lean_object* v_op_369_; lean_object* v_operand_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___y_374_; 
v_op_369_ = lean_ctor_get(v_a_330_, 1);
lean_inc(v_op_369_);
v_operand_370_ = lean_ctor_get(v_a_330_, 2);
lean_inc_ref(v_operand_370_);
lean_dec_ref_known(v_a_330_, 3);
v___x_371_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__19, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__19_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__19);
lean_inc(v_w_329_);
v___x_372_ = l_Lean_mkNatLit(v_w_329_);
switch(lean_obj_tag(v_op_369_))
{
case 0:
{
lean_object* v___x_377_; 
v___x_377_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__3, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__3);
v___y_374_ = v___x_377_;
goto v___jp_373_;
}
case 1:
{
lean_object* v_n_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v_n_378_ = lean_ctor_get(v_op_369_, 0);
lean_inc(v_n_378_);
lean_dec_ref_known(v_op_369_, 1);
v___x_379_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__6, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__6);
v___x_380_ = l_Lean_mkNatLit(v_n_378_);
v___x_381_ = l_Lean_Expr_app___override(v___x_379_, v___x_380_);
v___y_374_ = v___x_381_;
goto v___jp_373_;
}
case 2:
{
lean_object* v_n_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_n_382_ = lean_ctor_get(v_op_369_, 0);
lean_inc(v_n_382_);
lean_dec_ref_known(v_op_369_, 1);
v___x_383_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__9, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__9);
v___x_384_ = l_Lean_mkNatLit(v_n_382_);
v___x_385_ = l_Lean_Expr_app___override(v___x_383_, v___x_384_);
v___y_374_ = v___x_385_;
goto v___jp_373_;
}
case 3:
{
lean_object* v_n_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v_n_386_ = lean_ctor_get(v_op_369_, 0);
lean_inc(v_n_386_);
lean_dec_ref_known(v_op_369_, 1);
v___x_387_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__12, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__12);
v___x_388_ = l_Lean_mkNatLit(v_n_386_);
v___x_389_ = l_Lean_Expr_app___override(v___x_387_, v___x_388_);
v___y_374_ = v___x_389_;
goto v___jp_373_;
}
case 4:
{
lean_object* v___x_390_; 
v___x_390_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__15, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__15);
v___y_374_ = v___x_390_;
goto v___jp_373_;
}
case 5:
{
lean_object* v___x_391_; 
v___x_391_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__18, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__18_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__18);
v___y_374_ = v___x_391_;
goto v___jp_373_;
}
default: 
{
lean_object* v___x_392_; 
v___x_392_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__21, &l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__21_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVUnOp___lam__0___closed__21);
v___y_374_ = v___x_392_;
goto v___jp_373_;
}
}
v___jp_373_:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_329_, v_operand_370_);
v___x_376_ = l_Lean_mkApp3(v___x_371_, v___x_372_, v___y_374_, v___x_375_);
return v___x_376_;
}
}
case 5:
{
lean_object* v_l_393_; lean_object* v_r_394_; lean_object* v_lhs_395_; lean_object* v_rhs_396_; lean_object* v_wExpr_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v_proof_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v_l_393_ = lean_ctor_get(v_a_330_, 0);
lean_inc_n(v_l_393_, 2);
v_r_394_ = lean_ctor_get(v_a_330_, 1);
lean_inc_n(v_r_394_, 2);
v_lhs_395_ = lean_ctor_get(v_a_330_, 3);
lean_inc_ref(v_lhs_395_);
v_rhs_396_ = lean_ctor_get(v_a_330_, 4);
lean_inc_ref(v_rhs_396_);
lean_dec_ref_known(v_a_330_, 5);
v_wExpr_397_ = l_Lean_mkNatLit(v_w_329_);
v___x_398_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__25, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__25_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__25);
v___x_399_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__28, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__28);
lean_inc_ref(v_wExpr_397_);
v_proof_400_ = l_Lean_mkAppB(v___x_398_, v___x_399_, v_wExpr_397_);
v___x_401_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__31, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__31_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__31);
v___x_402_ = l_Lean_mkNatLit(v_l_393_);
v___x_403_ = l_Lean_mkNatLit(v_r_394_);
v___x_404_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_l_393_, v_lhs_395_);
v___x_405_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_r_394_, v_rhs_396_);
v___x_406_ = l_Lean_mkApp6(v___x_401_, v___x_402_, v___x_403_, v_wExpr_397_, v___x_404_, v___x_405_, v_proof_400_);
return v___x_406_;
}
case 6:
{
lean_object* v_w_407_; lean_object* v_n_408_; lean_object* v_expr_409_; lean_object* v_newWExpr_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v_proof_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_w_407_ = lean_ctor_get(v_a_330_, 0);
lean_inc_n(v_w_407_, 2);
v_n_408_ = lean_ctor_get(v_a_330_, 2);
lean_inc(v_n_408_);
v_expr_409_ = lean_ctor_get(v_a_330_, 3);
lean_inc_ref(v_expr_409_);
lean_dec_ref_known(v_a_330_, 4);
v_newWExpr_410_ = l_Lean_mkNatLit(v_w_329_);
v___x_411_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__25, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__25_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__25);
v___x_412_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__28, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__28_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__28);
lean_inc_ref(v_newWExpr_410_);
v_proof_413_ = l_Lean_mkAppB(v___x_411_, v___x_412_, v_newWExpr_410_);
v___x_414_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__34, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__34_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__34);
v___x_415_ = l_Lean_mkNatLit(v_w_407_);
v___x_416_ = l_Lean_mkNatLit(v_n_408_);
v___x_417_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_407_, v_expr_409_);
v___x_418_ = l_Lean_mkApp5(v___x_414_, v___x_415_, v_newWExpr_410_, v___x_416_, v___x_417_, v_proof_413_);
return v___x_418_;
}
case 7:
{
lean_object* v_n_419_; lean_object* v_lhs_420_; lean_object* v_rhs_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v_n_419_ = lean_ctor_get(v_a_330_, 1);
lean_inc_n(v_n_419_, 2);
v_lhs_420_ = lean_ctor_get(v_a_330_, 2);
lean_inc_ref(v_lhs_420_);
v_rhs_421_ = lean_ctor_get(v_a_330_, 3);
lean_inc_ref(v_rhs_421_);
lean_dec_ref_known(v_a_330_, 4);
v___x_422_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__37, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__37_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__37);
lean_inc(v_w_329_);
v___x_423_ = l_Lean_mkNatLit(v_w_329_);
v___x_424_ = l_Lean_mkNatLit(v_n_419_);
v___x_425_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_329_, v_lhs_420_);
v___x_426_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_n_419_, v_rhs_421_);
v___x_427_ = l_Lean_mkApp4(v___x_422_, v___x_423_, v___x_424_, v___x_425_, v___x_426_);
return v___x_427_;
}
case 8:
{
lean_object* v_n_428_; lean_object* v_lhs_429_; lean_object* v_rhs_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v_n_428_ = lean_ctor_get(v_a_330_, 1);
lean_inc_n(v_n_428_, 2);
v_lhs_429_ = lean_ctor_get(v_a_330_, 2);
lean_inc_ref(v_lhs_429_);
v_rhs_430_ = lean_ctor_get(v_a_330_, 3);
lean_inc_ref(v_rhs_430_);
lean_dec_ref_known(v_a_330_, 4);
v___x_431_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__40, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__40_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__40);
lean_inc(v_w_329_);
v___x_432_ = l_Lean_mkNatLit(v_w_329_);
v___x_433_ = l_Lean_mkNatLit(v_n_428_);
v___x_434_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_329_, v_lhs_429_);
v___x_435_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_n_428_, v_rhs_430_);
v___x_436_ = l_Lean_mkApp4(v___x_431_, v___x_432_, v___x_433_, v___x_434_, v___x_435_);
return v___x_436_;
}
default: 
{
lean_object* v_n_437_; lean_object* v_lhs_438_; lean_object* v_rhs_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v_n_437_ = lean_ctor_get(v_a_330_, 1);
lean_inc_n(v_n_437_, 2);
v_lhs_438_ = lean_ctor_get(v_a_330_, 2);
lean_inc_ref(v_lhs_438_);
v_rhs_439_ = lean_ctor_get(v_a_330_, 3);
lean_inc_ref(v_rhs_439_);
lean_dec_ref_known(v_a_330_, 4);
v___x_440_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__43, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__43_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go___closed__43);
lean_inc(v_w_329_);
v___x_441_ = l_Lean_mkNatLit(v_w_329_);
v___x_442_ = l_Lean_mkNatLit(v_n_437_);
v___x_443_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_329_, v_lhs_438_);
v___x_444_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_n_437_, v_rhs_439_);
v___x_445_ = l_Lean_mkApp4(v___x_440_, v___x_441_, v___x_442_, v___x_443_, v___x_444_);
return v___x_445_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___lam__0(lean_object* v_w_446_, lean_object* v_x_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_446_, v_x_447_);
return v___x_448_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__1(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_454_ = lean_box(0);
v___x_455_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__0));
v___x_456_ = l_Lean_mkConst(v___x_455_, v___x_454_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr(lean_object* v_w_457_){
_start:
{
lean_object* v___f_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
lean_inc(v_w_457_);
v___f_458_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___lam__0), 2, 1);
lean_closure_set(v___f_458_, 0, v_w_457_);
v___x_459_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__1, &l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr___closed__1);
v___x_460_ = l_Lean_mkNatLit(v_w_457_);
v___x_461_ = l_Lean_Expr_app___override(v___x_459_, v___x_460_);
v___x_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_462_, 0, v___f_458_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__3(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_471_ = lean_box(0);
v___x_472_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__2));
v___x_473_ = l_Lean_mkConst(v___x_472_, v___x_471_);
return v___x_473_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__6(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_481_ = lean_box(0);
v___x_482_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__5));
v___x_483_ = l_Lean_mkConst(v___x_482_, v___x_481_);
return v___x_483_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0(uint8_t v_x_484_){
_start:
{
if (v_x_484_ == 0)
{
lean_object* v___x_485_; 
v___x_485_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__3, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__3);
return v___x_485_;
}
else
{
lean_object* v___x_486_; 
v___x_486_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__6, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__6);
return v___x_486_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_484_ = stack[0].m_num;
lean_object* v_res_487_;
v_res_487_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0(v_x_484_);
stack->m_obj
 = v_res_487_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___boxed(lean_object* v_x_488_){
_start:
{
uint8_t v_x_boxed_489_; lean_object* v_res_490_; 
v_x_boxed_489_ = lean_unbox(v_x_488_);
v_res_490_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0(v_x_boxed_489_);
return v_res_490_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__2(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_497_ = lean_box(0);
v___x_498_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__1));
v___x_499_ = l_Lean_mkConst(v___x_498_, v___x_497_);
return v___x_499_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__3(void){
_start:
{
lean_object* v___x_500_; lean_object* v___f_501_; lean_object* v___x_502_; 
v___x_500_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__2, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__2);
v___f_501_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__0));
v___x_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_502_, 0, v___f_501_);
lean_ctor_set(v___x_502_, 1, v___x_500_);
return v___x_502_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred(void){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__3, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___closed__3);
return v___x_503_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__2(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_511_ = lean_box(0);
v___x_512_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__1));
v___x_513_ = l_Lean_mkConst(v___x_512_, v___x_511_);
return v___x_513_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__4(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_520_ = lean_box(0);
v___x_521_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__3));
v___x_522_ = l_Lean_mkConst(v___x_521_, v___x_520_);
return v___x_522_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__7(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_530_ = lean_box(0);
v___x_531_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__6));
v___x_532_ = l_Lean_mkConst(v___x_531_, v___x_530_);
return v___x_532_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__9(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_539_ = lean_box(0);
v___x_540_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__8));
v___x_541_ = l_Lean_mkConst(v___x_540_, v___x_539_);
return v___x_541_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0(uint8_t v_x_542_){
_start:
{
switch(v_x_542_)
{
case 0:
{
lean_object* v___x_543_; 
v___x_543_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__2);
return v___x_543_;
}
case 1:
{
lean_object* v___x_544_; 
v___x_544_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__4, &l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__4);
return v___x_544_;
}
case 2:
{
lean_object* v___x_545_; 
v___x_545_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__7, &l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__7);
return v___x_545_;
}
default: 
{
lean_object* v___x_546_; 
v___x_546_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__9, &l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__9);
return v___x_546_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_542_ = stack[0].m_num;
lean_object* v_res_547_;
v_res_547_ = l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0(v_x_542_);
stack->m_obj
 = v_res_547_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___boxed(lean_object* v_x_548_){
_start:
{
uint8_t v_x_boxed_549_; lean_object* v_res_550_; 
v_x_boxed_549_ = lean_unbox(v_x_548_);
v_res_550_ = l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0(v_x_boxed_549_);
return v_res_550_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__2(void){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_557_ = lean_box(0);
v___x_558_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__1));
v___x_559_ = l_Lean_mkConst(v___x_558_, v___x_557_);
return v___x_559_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__3(void){
_start:
{
lean_object* v___x_560_; lean_object* v___f_561_; lean_object* v___x_562_; 
v___x_560_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__2, &l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__2);
v___f_561_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__0));
v___x_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_562_, 0, v___f_561_);
lean_ctor_set(v___x_562_, 1, v___x_560_);
return v___x_562_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate(void){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__3, &l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___closed__3);
return v___x_563_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__2(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_571_ = lean_box(0);
v___x_572_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__1));
v___x_573_ = l_Lean_mkConst(v___x_572_, v___x_571_);
return v___x_573_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__5(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_581_ = lean_box(0);
v___x_582_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__4));
v___x_583_ = l_Lean_mkConst(v___x_582_, v___x_581_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go(lean_object* v_a_584_){
_start:
{
if (lean_obj_tag(v_a_584_) == 0)
{
lean_object* v_w_585_; lean_object* v_lhs_586_; uint8_t v_op_587_; lean_object* v_rhs_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___y_593_; 
v_w_585_ = lean_ctor_get(v_a_584_, 0);
lean_inc_n(v_w_585_, 3);
v_lhs_586_ = lean_ctor_get(v_a_584_, 1);
lean_inc_ref(v_lhs_586_);
v_op_587_ = lean_ctor_get_uint8(v_a_584_, sizeof(void*)*3);
v_rhs_588_ = lean_ctor_get(v_a_584_, 2);
lean_inc_ref(v_rhs_588_);
lean_dec_ref_known(v_a_584_, 3);
v___x_589_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__2, &l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__2);
v___x_590_ = l_Lean_mkNatLit(v_w_585_);
v___x_591_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_585_, v_lhs_586_);
if (v_op_587_ == 0)
{
lean_object* v___x_596_; 
v___x_596_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__3, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__3);
v___y_593_ = v___x_596_;
goto v___jp_592_;
}
else
{
lean_object* v___x_597_; 
v___x_597_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__6, &l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__6_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVBinPred___lam__0___closed__6);
v___y_593_ = v___x_597_;
goto v___jp_592_;
}
v___jp_592_:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_585_, v_rhs_588_);
lean_inc_ref(v___y_593_);
v___x_595_ = l_Lean_mkApp4(v___x_589_, v___x_590_, v___x_591_, v___y_593_, v___x_594_);
return v___x_595_;
}
}
else
{
lean_object* v_w_598_; lean_object* v_expr_599_; lean_object* v_idx_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v_w_598_ = lean_ctor_get(v_a_584_, 0);
lean_inc_n(v_w_598_, 2);
v_expr_599_ = lean_ctor_get(v_a_584_, 1);
lean_inc_ref(v_expr_599_);
v_idx_600_ = lean_ctor_get(v_a_584_, 2);
lean_inc(v_idx_600_);
lean_dec_ref_known(v_a_584_, 3);
v___x_601_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__5, &l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVPred_go___closed__5);
v___x_602_ = l_Lean_mkNatLit(v_w_598_);
v___x_603_ = l_Lean_Meta_Tactic_BVDecide_instToExprBVExpr_go(v_w_598_, v_expr_599_);
v___x_604_ = l_Lean_mkNatLit(v_idx_600_);
v___x_605_ = l_Lean_mkApp3(v___x_601_, v___x_602_, v___x_603_, v___x_604_);
return v___x_605_;
}
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__2(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_612_ = lean_box(0);
v___x_613_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__1));
v___x_614_ = l_Lean_mkConst(v___x_613_, v___x_612_);
return v___x_614_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__3(void){
_start:
{
lean_object* v___x_615_; lean_object* v___f_616_; lean_object* v___x_617_; 
v___x_615_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__2, &l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__2);
v___f_616_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__0));
v___x_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_617_, 0, v___f_616_);
lean_ctor_set(v___x_617_, 1, v___x_615_);
return v___x_617_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVPred(void){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__3, &l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBVPred___closed__3);
return v___x_618_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__3(void){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_627_ = lean_box(0);
v___x_628_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__2));
v___x_629_ = l_Lean_mkConst(v___x_628_, v___x_627_);
return v___x_629_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__5(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_636_ = lean_box(0);
v___x_637_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__4));
v___x_638_ = l_Lean_mkConst(v___x_637_, v___x_636_);
return v___x_638_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__9(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = lean_box(0);
v___x_645_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__8));
v___x_646_ = l_Lean_mkConst(v___x_645_, v___x_644_);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__12(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_651_ = lean_box(0);
v___x_652_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__11));
v___x_653_ = l_Lean_mkConst(v___x_652_, v___x_651_);
return v___x_653_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__14(void){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_660_ = lean_box(0);
v___x_661_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__13));
v___x_662_ = l_Lean_mkConst(v___x_661_, v___x_660_);
return v___x_662_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__17(void){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_670_ = lean_box(0);
v___x_671_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__16));
v___x_672_ = l_Lean_mkConst(v___x_671_, v___x_670_);
return v___x_672_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__20(void){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_680_ = lean_box(0);
v___x_681_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__19));
v___x_682_ = l_Lean_mkConst(v___x_681_, v___x_680_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg(lean_object* v_inst_683_, lean_object* v_a_684_){
_start:
{
switch(lean_obj_tag(v_a_684_))
{
case 0:
{
lean_object* v_a_685_; lean_object* v_toExpr_686_; lean_object* v_toTypeExpr_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; 
v_a_685_ = lean_ctor_get(v_a_684_, 0);
lean_inc(v_a_685_);
lean_dec_ref_known(v_a_684_, 1);
v_toExpr_686_ = lean_ctor_get(v_inst_683_, 0);
lean_inc_ref(v_toExpr_686_);
v_toTypeExpr_687_ = lean_ctor_get(v_inst_683_, 1);
lean_inc_ref(v_toTypeExpr_687_);
lean_dec_ref(v_inst_683_);
v___x_688_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__3, &l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__3_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__3);
v___x_689_ = lean_apply_1(v_toExpr_686_, v_a_685_);
v___x_690_ = l_Lean_mkAppB(v___x_688_, v_toTypeExpr_687_, v___x_689_);
return v___x_690_;
}
case 1:
{
uint8_t v_a_691_; lean_object* v_toTypeExpr_692_; lean_object* v___x_693_; 
v_a_691_ = lean_ctor_get_uint8(v_a_684_, 0);
lean_dec_ref_known(v_a_684_, 0);
v_toTypeExpr_692_ = lean_ctor_get(v_inst_683_, 1);
lean_inc_ref(v_toTypeExpr_692_);
lean_dec_ref(v_inst_683_);
v___x_693_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__5, &l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__5);
if (v_a_691_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__9, &l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__9);
v___x_695_ = l_Lean_mkAppB(v___x_693_, v_toTypeExpr_692_, v___x_694_);
return v___x_695_;
}
else
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__12, &l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__12_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__12);
v___x_697_ = l_Lean_mkAppB(v___x_693_, v_toTypeExpr_692_, v___x_696_);
return v___x_697_;
}
}
case 2:
{
lean_object* v_a_698_; lean_object* v_toTypeExpr_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v_a_698_ = lean_ctor_get(v_a_684_, 0);
lean_inc_ref(v_a_698_);
lean_dec_ref_known(v_a_684_, 1);
v_toTypeExpr_699_ = lean_ctor_get(v_inst_683_, 1);
lean_inc_ref(v_toTypeExpr_699_);
v___x_700_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__14, &l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__14_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__14);
v___x_701_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg(v_inst_683_, v_a_698_);
v___x_702_ = l_Lean_mkAppB(v___x_700_, v_toTypeExpr_699_, v___x_701_);
return v___x_702_;
}
case 3:
{
uint8_t v_a_703_; lean_object* v_a_704_; lean_object* v_a_705_; lean_object* v_toTypeExpr_706_; lean_object* v___x_707_; lean_object* v___y_709_; 
v_a_703_ = lean_ctor_get_uint8(v_a_684_, sizeof(void*)*2);
v_a_704_ = lean_ctor_get(v_a_684_, 0);
lean_inc_ref(v_a_704_);
v_a_705_ = lean_ctor_get(v_a_684_, 1);
lean_inc_ref(v_a_705_);
lean_dec_ref_known(v_a_684_, 2);
v_toTypeExpr_706_ = lean_ctor_get(v_inst_683_, 1);
lean_inc_ref(v_toTypeExpr_706_);
v___x_707_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__17, &l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__17_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__17);
switch(v_a_703_)
{
case 0:
{
lean_object* v___x_713_; 
v___x_713_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__2, &l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__2);
v___y_709_ = v___x_713_;
goto v___jp_708_;
}
case 1:
{
lean_object* v___x_714_; 
v___x_714_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__4, &l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__4);
v___y_709_ = v___x_714_;
goto v___jp_708_;
}
case 2:
{
lean_object* v___x_715_; 
v___x_715_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__7, &l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__7);
v___y_709_ = v___x_715_;
goto v___jp_708_;
}
default: 
{
lean_object* v___x_716_; 
v___x_716_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__9, &l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprGate___lam__0___closed__9);
v___y_709_ = v___x_716_;
goto v___jp_708_;
}
}
v___jp_708_:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
lean_inc_ref(v_inst_683_);
v___x_710_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg(v_inst_683_, v_a_704_);
v___x_711_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg(v_inst_683_, v_a_705_);
lean_inc_ref(v___y_709_);
v___x_712_ = l_Lean_mkApp4(v___x_707_, v_toTypeExpr_706_, v___y_709_, v___x_710_, v___x_711_);
return v___x_712_;
}
}
default: 
{
lean_object* v_a_717_; lean_object* v_a_718_; lean_object* v_a_719_; lean_object* v_toTypeExpr_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v_a_717_ = lean_ctor_get(v_a_684_, 0);
lean_inc_ref(v_a_717_);
v_a_718_ = lean_ctor_get(v_a_684_, 1);
lean_inc_ref(v_a_718_);
v_a_719_ = lean_ctor_get(v_a_684_, 2);
lean_inc_ref(v_a_719_);
lean_dec_ref_known(v_a_684_, 3);
v_toTypeExpr_720_ = lean_ctor_get(v_inst_683_, 1);
lean_inc_ref(v_toTypeExpr_720_);
v___x_721_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__20, &l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__20_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__20);
lean_inc_ref_n(v_inst_683_, 2);
v___x_722_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg(v_inst_683_, v_a_717_);
v___x_723_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg(v_inst_683_, v_a_718_);
v___x_724_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg(v_inst_683_, v_a_719_);
v___x_725_ = l_Lean_mkApp4(v___x_721_, v_toTypeExpr_720_, v___x_722_, v___x_723_, v___x_724_);
return v___x_725_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go(lean_object* v_00_u03b1_726_, lean_object* v_inst_727_, lean_object* v_a_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg(v_inst_727_, v_a_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___lam__0(lean_object* v_inst_730_, lean_object* v_x_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg(v_inst_730_, v_x_731_);
return v___x_732_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__1(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_738_ = lean_box(0);
v___x_739_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__0));
v___x_740_ = l_Lean_mkConst(v___x_739_, v___x_738_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg(lean_object* v_inst_741_){
_start:
{
lean_object* v_toTypeExpr_742_; lean_object* v___f_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v_toTypeExpr_742_ = lean_ctor_get(v_inst_741_, 1);
lean_inc_ref(v_toTypeExpr_742_);
v___f_743_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___lam__0), 2, 1);
lean_closure_set(v___f_743_, 0, v_inst_741_);
v___x_744_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg___closed__1);
v___x_745_ = l_Lean_Expr_app___override(v___x_744_, v_toTypeExpr_742_);
v___x_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_746_, 0, v___f_743_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr(lean_object* v_00_u03b1_747_, lean_object* v_inst_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr___redArg(v_inst_748_);
return v___x_749_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper___closed__2(void){
_start:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_754_ = lean_box(0);
v___x_755_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper___closed__1));
v___x_756_ = l_Lean_mkConst(v___x_755_, v___x_754_);
return v___x_756_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper(lean_object* v_e_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_765_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper___closed__2, &l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper___closed__2_once, _init_l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper___closed__2);
v___x_766_ = l_Lean_Expr_app___override(v___x_765_, v_e_757_);
v___x_767_ = l_Lean_Meta_Sym_shareCommonInc(v___x_766_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_);
return v___x_767_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_757_ = stack[0].m_obj;
lean_object* v_a_758_ = stack[1].m_obj;
lean_object* v_a_759_ = stack[2].m_obj;
lean_object* v_a_760_ = stack[3].m_obj;
lean_object* v_a_761_ = stack[4].m_obj;
lean_object* v_a_762_ = stack[5].m_obj;
lean_object* v_a_763_ = stack[6].m_obj;
lean_object* v_res_768_;
v_res_768_ = l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper(v_e_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_);
stack->m_obj
 = v_res_768_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper___boxed(lean_object* v_e_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper(v_e_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
lean_dec(v_a_773_);
lean_dec_ref(v_a_772_);
lean_dec(v_a_771_);
lean_dec_ref(v_a_770_);
return v_res_777_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_FunAtom_atomExpr(lean_object* v_funAtom_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_){
_start:
{
uint8_t v_isBoolAtom_786_; 
v_isBoolAtom_786_ = lean_ctor_get_uint8(v_funAtom_778_, sizeof(void*)*1);
if (v_isBoolAtom_786_ == 0)
{
lean_object* v_funExpr_787_; lean_object* v___x_788_; 
v_funExpr_787_ = lean_ctor_get(v_funAtom_778_, 0);
lean_inc_ref(v_funExpr_787_);
lean_dec_ref(v_funAtom_778_);
v___x_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_788_, 0, v_funExpr_787_);
return v___x_788_;
}
else
{
lean_object* v_funExpr_789_; lean_object* v___x_790_; 
v_funExpr_789_ = lean_ctor_get(v_funAtom_778_, 0);
lean_inc_ref(v_funExpr_789_);
lean_dec_ref(v_funAtom_778_);
v___x_790_ = l_Lean_Meta_Tactic_BVDecide_mkBoolAtomWrapper(v_funExpr_789_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_);
return v___x_790_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_FunAtom_atomExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_funAtom_778_ = stack[0].m_obj;
lean_object* v_a_779_ = stack[1].m_obj;
lean_object* v_a_780_ = stack[2].m_obj;
lean_object* v_a_781_ = stack[3].m_obj;
lean_object* v_a_782_ = stack[4].m_obj;
lean_object* v_a_783_ = stack[5].m_obj;
lean_object* v_a_784_ = stack[6].m_obj;
lean_object* v_res_791_;
v_res_791_ = l_Lean_Meta_Tactic_BVDecide_FunAtom_atomExpr(v_funAtom_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_);
stack->m_obj
 = v_res_791_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_FunAtom_atomExpr___boxed(lean_object* v_funAtom_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Lean_Meta_Tactic_BVDecide_FunAtom_atomExpr(v_funAtom_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
lean_dec(v_a_796_);
lean_dec_ref(v_a_795_);
lean_dec(v_a_794_);
lean_dec_ref(v_a_793_);
return v_res_800_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg(lean_object* v_a_801_, lean_object* v_x_802_){
_start:
{
if (lean_obj_tag(v_x_802_) == 0)
{
uint8_t v___x_803_; 
v___x_803_ = 0;
return v___x_803_;
}
else
{
lean_object* v_key_804_; lean_object* v_tail_805_; size_t v___x_806_; size_t v___x_807_; uint8_t v___x_808_; 
v_key_804_ = lean_ctor_get(v_x_802_, 0);
v_tail_805_ = lean_ctor_get(v_x_802_, 2);
v___x_806_ = lean_ptr_addr(v_key_804_);
v___x_807_ = lean_ptr_addr(v_a_801_);
v___x_808_ = lean_usize_dec_eq(v___x_806_, v___x_807_);
if (v___x_808_ == 0)
{
v_x_802_ = v_tail_805_;
goto _start;
}
else
{
return v___x_808_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_801_ = stack[0].m_obj;
lean_object* v_x_802_ = stack[1].m_obj;
uint8_t v_res_810_;
v_res_810_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg(v_a_801_, v_x_802_);
stack->m_num = v_res_810_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg___boxed(lean_object* v_a_811_, lean_object* v_x_812_){
_start:
{
uint8_t v_res_813_; lean_object* v_r_814_; 
v_res_813_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg(v_a_811_, v_x_812_);
lean_dec(v_x_812_);
lean_dec_ref(v_a_811_);
v_r_814_ = lean_box(v_res_813_);
return v_r_814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_815_, lean_object* v_x_816_){
_start:
{
if (lean_obj_tag(v_x_816_) == 0)
{
return v_x_815_;
}
else
{
lean_object* v_key_817_; lean_object* v_value_818_; lean_object* v_tail_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_845_; 
v_key_817_ = lean_ctor_get(v_x_816_, 0);
v_value_818_ = lean_ctor_get(v_x_816_, 1);
v_tail_819_ = lean_ctor_get(v_x_816_, 2);
v_isSharedCheck_845_ = !lean_is_exclusive(v_x_816_);
if (v_isSharedCheck_845_ == 0)
{
v___x_821_ = v_x_816_;
v_isShared_822_ = v_isSharedCheck_845_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_tail_819_);
lean_inc(v_value_818_);
lean_inc(v_key_817_);
lean_dec(v_x_816_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_845_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_823_; size_t v___x_824_; size_t v___x_825_; size_t v___x_826_; uint64_t v___x_827_; uint64_t v___x_828_; uint64_t v___x_829_; uint64_t v_fold_830_; uint64_t v___x_831_; uint64_t v___x_832_; uint64_t v___x_833_; size_t v___x_834_; size_t v___x_835_; size_t v___x_836_; size_t v___x_837_; size_t v___x_838_; lean_object* v___x_839_; lean_object* v___x_841_; 
v___x_823_ = lean_array_get_size(v_x_815_);
v___x_824_ = lean_ptr_addr(v_key_817_);
v___x_825_ = ((size_t)3ULL);
v___x_826_ = lean_usize_shift_right(v___x_824_, v___x_825_);
v___x_827_ = lean_usize_to_uint64(v___x_826_);
v___x_828_ = 32ULL;
v___x_829_ = lean_uint64_shift_right(v___x_827_, v___x_828_);
v_fold_830_ = lean_uint64_xor(v___x_827_, v___x_829_);
v___x_831_ = 16ULL;
v___x_832_ = lean_uint64_shift_right(v_fold_830_, v___x_831_);
v___x_833_ = lean_uint64_xor(v_fold_830_, v___x_832_);
v___x_834_ = lean_uint64_to_usize(v___x_833_);
v___x_835_ = lean_usize_of_nat(v___x_823_);
v___x_836_ = ((size_t)1ULL);
v___x_837_ = lean_usize_sub(v___x_835_, v___x_836_);
v___x_838_ = lean_usize_land(v___x_834_, v___x_837_);
v___x_839_ = lean_array_uget_borrowed(v_x_815_, v___x_838_);
lean_inc(v___x_839_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 2, v___x_839_);
v___x_841_ = v___x_821_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_key_817_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v_value_818_);
lean_ctor_set(v_reuseFailAlloc_844_, 2, v___x_839_);
v___x_841_ = v_reuseFailAlloc_844_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
lean_object* v___x_842_; 
v___x_842_ = lean_array_uset(v_x_815_, v___x_838_, v___x_841_);
v_x_815_ = v___x_842_;
v_x_816_ = v_tail_819_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4___redArg(lean_object* v_i_846_, lean_object* v_source_847_, lean_object* v_target_848_){
_start:
{
lean_object* v___x_849_; uint8_t v___x_850_; 
v___x_849_ = lean_array_get_size(v_source_847_);
v___x_850_ = lean_nat_dec_lt(v_i_846_, v___x_849_);
if (v___x_850_ == 0)
{
lean_dec_ref(v_source_847_);
lean_dec(v_i_846_);
return v_target_848_;
}
else
{
lean_object* v_es_851_; lean_object* v___x_852_; lean_object* v_source_853_; lean_object* v_target_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v_es_851_ = lean_array_fget(v_source_847_, v_i_846_);
v___x_852_ = lean_box(0);
v_source_853_ = lean_array_fset(v_source_847_, v_i_846_, v___x_852_);
v_target_854_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4_spec__5___redArg(v_target_848_, v_es_851_);
v___x_855_ = lean_unsigned_to_nat(1u);
v___x_856_ = lean_nat_add(v_i_846_, v___x_855_);
lean_dec(v_i_846_);
v_i_846_ = v___x_856_;
v_source_847_ = v_source_853_;
v_target_848_ = v_target_854_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3___redArg(lean_object* v_data_858_){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v_nbuckets_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_859_ = lean_array_get_size(v_data_858_);
v___x_860_ = lean_unsigned_to_nat(2u);
v_nbuckets_861_ = lean_nat_mul(v___x_859_, v___x_860_);
v___x_862_ = lean_unsigned_to_nat(0u);
v___x_863_ = lean_box(0);
v___x_864_ = lean_mk_array(v_nbuckets_861_, v___x_863_);
v___x_865_ = lean_array_propagate_mark(v_data_858_, v___x_864_);
v___x_866_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4___redArg(v___x_862_, v_data_858_, v___x_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__4___redArg(lean_object* v_a_867_, lean_object* v_b_868_, lean_object* v_x_869_){
_start:
{
if (lean_obj_tag(v_x_869_) == 0)
{
lean_dec(v_b_868_);
lean_dec_ref(v_a_867_);
return v_x_869_;
}
else
{
lean_object* v_key_870_; lean_object* v_value_871_; lean_object* v_tail_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_886_; 
v_key_870_ = lean_ctor_get(v_x_869_, 0);
v_value_871_ = lean_ctor_get(v_x_869_, 1);
v_tail_872_ = lean_ctor_get(v_x_869_, 2);
v_isSharedCheck_886_ = !lean_is_exclusive(v_x_869_);
if (v_isSharedCheck_886_ == 0)
{
v___x_874_ = v_x_869_;
v_isShared_875_ = v_isSharedCheck_886_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_tail_872_);
lean_inc(v_value_871_);
lean_inc(v_key_870_);
lean_dec(v_x_869_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_886_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
size_t v___x_876_; size_t v___x_877_; uint8_t v___x_878_; 
v___x_876_ = lean_ptr_addr(v_key_870_);
v___x_877_ = lean_ptr_addr(v_a_867_);
v___x_878_ = lean_usize_dec_eq(v___x_876_, v___x_877_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_879_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__4___redArg(v_a_867_, v_b_868_, v_tail_872_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 2, v___x_879_);
v___x_881_ = v___x_874_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_key_870_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v_value_871_);
lean_ctor_set(v_reuseFailAlloc_882_, 2, v___x_879_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
else
{
lean_object* v___x_884_; 
lean_dec(v_value_871_);
lean_dec(v_key_870_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 1, v_b_868_);
lean_ctor_set(v___x_874_, 0, v_a_867_);
v___x_884_ = v___x_874_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_867_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_b_868_);
lean_ctor_set(v_reuseFailAlloc_885_, 2, v_tail_872_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(lean_object* v_m_887_, lean_object* v_a_888_, lean_object* v_b_889_){
_start:
{
lean_object* v_size_890_; lean_object* v_buckets_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_937_; 
v_size_890_ = lean_ctor_get(v_m_887_, 0);
v_buckets_891_ = lean_ctor_get(v_m_887_, 1);
v_isSharedCheck_937_ = !lean_is_exclusive(v_m_887_);
if (v_isSharedCheck_937_ == 0)
{
v___x_893_ = v_m_887_;
v_isShared_894_ = v_isSharedCheck_937_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_buckets_891_);
lean_inc(v_size_890_);
lean_dec(v_m_887_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_937_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_895_; size_t v___x_896_; size_t v___x_897_; size_t v___x_898_; uint64_t v___x_899_; uint64_t v___x_900_; uint64_t v___x_901_; uint64_t v_fold_902_; uint64_t v___x_903_; uint64_t v___x_904_; uint64_t v___x_905_; size_t v___x_906_; size_t v___x_907_; size_t v___x_908_; size_t v___x_909_; size_t v___x_910_; lean_object* v_bkt_911_; uint8_t v___x_912_; 
v___x_895_ = lean_array_get_size(v_buckets_891_);
v___x_896_ = lean_ptr_addr(v_a_888_);
v___x_897_ = ((size_t)3ULL);
v___x_898_ = lean_usize_shift_right(v___x_896_, v___x_897_);
v___x_899_ = lean_usize_to_uint64(v___x_898_);
v___x_900_ = 32ULL;
v___x_901_ = lean_uint64_shift_right(v___x_899_, v___x_900_);
v_fold_902_ = lean_uint64_xor(v___x_899_, v___x_901_);
v___x_903_ = 16ULL;
v___x_904_ = lean_uint64_shift_right(v_fold_902_, v___x_903_);
v___x_905_ = lean_uint64_xor(v_fold_902_, v___x_904_);
v___x_906_ = lean_uint64_to_usize(v___x_905_);
v___x_907_ = lean_usize_of_nat(v___x_895_);
v___x_908_ = ((size_t)1ULL);
v___x_909_ = lean_usize_sub(v___x_907_, v___x_908_);
v___x_910_ = lean_usize_land(v___x_906_, v___x_909_);
v_bkt_911_ = lean_array_uget_borrowed(v_buckets_891_, v___x_910_);
v___x_912_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg(v_a_888_, v_bkt_911_);
if (v___x_912_ == 0)
{
lean_object* v___x_913_; lean_object* v_size_x27_914_; lean_object* v___x_915_; lean_object* v_buckets_x27_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_913_ = lean_unsigned_to_nat(1u);
v_size_x27_914_ = lean_nat_add(v_size_890_, v___x_913_);
lean_dec(v_size_890_);
lean_inc(v_bkt_911_);
v___x_915_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_915_, 0, v_a_888_);
lean_ctor_set(v___x_915_, 1, v_b_889_);
lean_ctor_set(v___x_915_, 2, v_bkt_911_);
v_buckets_x27_916_ = lean_array_uset(v_buckets_891_, v___x_910_, v___x_915_);
v___x_917_ = lean_unsigned_to_nat(4u);
v___x_918_ = lean_nat_mul(v_size_x27_914_, v___x_917_);
v___x_919_ = lean_unsigned_to_nat(3u);
v___x_920_ = lean_nat_div(v___x_918_, v___x_919_);
lean_dec(v___x_918_);
v___x_921_ = lean_array_get_size(v_buckets_x27_916_);
v___x_922_ = lean_nat_dec_le(v___x_920_, v___x_921_);
lean_dec(v___x_920_);
if (v___x_922_ == 0)
{
lean_object* v_val_923_; lean_object* v___x_925_; 
v_val_923_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3___redArg(v_buckets_x27_916_);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 1, v_val_923_);
lean_ctor_set(v___x_893_, 0, v_size_x27_914_);
v___x_925_ = v___x_893_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_size_x27_914_);
lean_ctor_set(v_reuseFailAlloc_926_, 1, v_val_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
else
{
lean_object* v___x_928_; 
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 1, v_buckets_x27_916_);
lean_ctor_set(v___x_893_, 0, v_size_x27_914_);
v___x_928_ = v___x_893_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_size_x27_914_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_buckets_x27_916_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
else
{
lean_object* v___x_930_; lean_object* v_buckets_x27_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_935_; 
lean_inc(v_bkt_911_);
v___x_930_ = lean_box(0);
v_buckets_x27_931_ = lean_array_uset(v_buckets_891_, v___x_910_, v___x_930_);
v___x_932_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__4___redArg(v_a_888_, v_b_889_, v_bkt_911_);
v___x_933_ = lean_array_uset(v_buckets_x27_931_, v___x_910_, v___x_932_);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 1, v___x_933_);
v___x_935_ = v___x_893_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_size_890_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v___x_933_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg(lean_object* v_a_938_, lean_object* v_x_939_){
_start:
{
if (lean_obj_tag(v_x_939_) == 0)
{
lean_object* v___x_940_; 
v___x_940_ = lean_box(0);
return v___x_940_;
}
else
{
lean_object* v_key_941_; lean_object* v_value_942_; lean_object* v_tail_943_; size_t v___x_944_; size_t v___x_945_; uint8_t v___x_946_; 
v_key_941_ = lean_ctor_get(v_x_939_, 0);
v_value_942_ = lean_ctor_get(v_x_939_, 1);
v_tail_943_ = lean_ctor_get(v_x_939_, 2);
v___x_944_ = lean_ptr_addr(v_key_941_);
v___x_945_ = lean_ptr_addr(v_a_938_);
v___x_946_ = lean_usize_dec_eq(v___x_944_, v___x_945_);
if (v___x_946_ == 0)
{
v_x_939_ = v_tail_943_;
goto _start;
}
else
{
lean_object* v___x_948_; 
lean_inc(v_value_942_);
v___x_948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_948_, 0, v_value_942_);
return v___x_948_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg___boxed(lean_object* v_a_949_, lean_object* v_x_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg(v_a_949_, v_x_950_);
lean_dec(v_x_950_);
lean_dec_ref(v_a_949_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(lean_object* v_m_952_, lean_object* v_a_953_){
_start:
{
lean_object* v_buckets_954_; lean_object* v___x_955_; size_t v___x_956_; size_t v___x_957_; size_t v___x_958_; uint64_t v___x_959_; uint64_t v___x_960_; uint64_t v___x_961_; uint64_t v_fold_962_; uint64_t v___x_963_; uint64_t v___x_964_; uint64_t v___x_965_; size_t v___x_966_; size_t v___x_967_; size_t v___x_968_; size_t v___x_969_; size_t v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v_buckets_954_ = lean_ctor_get(v_m_952_, 1);
v___x_955_ = lean_array_get_size(v_buckets_954_);
v___x_956_ = lean_ptr_addr(v_a_953_);
v___x_957_ = ((size_t)3ULL);
v___x_958_ = lean_usize_shift_right(v___x_956_, v___x_957_);
v___x_959_ = lean_usize_to_uint64(v___x_958_);
v___x_960_ = 32ULL;
v___x_961_ = lean_uint64_shift_right(v___x_959_, v___x_960_);
v_fold_962_ = lean_uint64_xor(v___x_959_, v___x_961_);
v___x_963_ = 16ULL;
v___x_964_ = lean_uint64_shift_right(v_fold_962_, v___x_963_);
v___x_965_ = lean_uint64_xor(v_fold_962_, v___x_964_);
v___x_966_ = lean_uint64_to_usize(v___x_965_);
v___x_967_ = lean_usize_of_nat(v___x_955_);
v___x_968_ = ((size_t)1ULL);
v___x_969_ = lean_usize_sub(v___x_967_, v___x_968_);
v___x_970_ = lean_usize_land(v___x_966_, v___x_969_);
v___x_971_ = lean_array_uget_borrowed(v_buckets_954_, v___x_970_);
v___x_972_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg(v_a_953_, v___x_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg___boxed(lean_object* v_m_973_, lean_object* v_a_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_m_973_, v_a_974_);
lean_dec_ref(v_a_974_);
lean_dec_ref(v_m_973_);
return v_res_975_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(lean_object* v_reified_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_){
_start:
{
lean_object* v_originalExpr_989_; lean_object* v_evalsAtAtoms_x27_990_; lean_object* v___x_991_; lean_object* v_evalsAtCache_992_; lean_object* v___x_993_; 
v_originalExpr_989_ = lean_ctor_get(v_reified_976_, 2);
lean_inc_ref(v_originalExpr_989_);
v_evalsAtAtoms_x27_990_ = lean_ctor_get(v_reified_976_, 3);
lean_inc_ref(v_evalsAtAtoms_x27_990_);
lean_dec_ref(v_reified_976_);
v___x_991_ = lean_st_ref_get(v_a_978_);
v_evalsAtCache_992_ = lean_ctor_get(v___x_991_, 3);
lean_inc_ref(v_evalsAtCache_992_);
lean_dec(v___x_991_);
v___x_993_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_evalsAtCache_992_, v_originalExpr_989_);
lean_dec_ref(v_evalsAtCache_992_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v___x_994_; 
lean_inc(v_a_987_);
lean_inc_ref(v_a_986_);
lean_inc(v_a_985_);
lean_inc_ref(v_a_984_);
lean_inc(v_a_983_);
lean_inc_ref(v_a_982_);
lean_inc(v_a_981_);
lean_inc_ref(v_a_980_);
lean_inc(v_a_979_);
lean_inc(v_a_978_);
lean_inc_ref(v_a_977_);
v___x_994_ = lean_apply_12(v_evalsAtAtoms_x27_990_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, lean_box(0));
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1017_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_997_ = v___x_994_;
v_isShared_998_ = v_isSharedCheck_1017_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1017_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_999_; lean_object* v_atoms_1000_; lean_object* v_atomsAssignmentExprCache_1001_; lean_object* v_atomsAssignmentMapCache_1002_; lean_object* v_evalsAtCache_1003_; lean_object* v_theoryState_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1016_; 
v___x_999_ = lean_st_ref_take(v_a_978_);
v_atoms_1000_ = lean_ctor_get(v___x_999_, 0);
v_atomsAssignmentExprCache_1001_ = lean_ctor_get(v___x_999_, 1);
v_atomsAssignmentMapCache_1002_ = lean_ctor_get(v___x_999_, 2);
v_evalsAtCache_1003_ = lean_ctor_get(v___x_999_, 3);
v_theoryState_1004_ = lean_ctor_get(v___x_999_, 4);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1006_ = v___x_999_;
v_isShared_1007_ = v_isSharedCheck_1016_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_theoryState_1004_);
lean_inc(v_evalsAtCache_1003_);
lean_inc(v_atomsAssignmentMapCache_1002_);
lean_inc(v_atomsAssignmentExprCache_1001_);
lean_inc(v_atoms_1000_);
lean_dec(v___x_999_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1016_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1008_; lean_object* v___x_1010_; 
lean_inc(v_a_995_);
v___x_1008_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v_evalsAtCache_1003_, v_originalExpr_989_, v_a_995_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 3, v___x_1008_);
v___x_1010_ = v___x_1006_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_atoms_1000_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v_atomsAssignmentExprCache_1001_);
lean_ctor_set(v_reuseFailAlloc_1015_, 2, v_atomsAssignmentMapCache_1002_);
lean_ctor_set(v_reuseFailAlloc_1015_, 3, v___x_1008_);
lean_ctor_set(v_reuseFailAlloc_1015_, 4, v_theoryState_1004_);
v___x_1010_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
lean_object* v___x_1011_; lean_object* v___x_1013_; 
v___x_1011_ = lean_st_ref_put(v_a_978_, v___x_1010_);
if (v_isShared_998_ == 0)
{
v___x_1013_ = v___x_997_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_995_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
}
else
{
lean_dec_ref(v_originalExpr_989_);
return v___x_994_;
}
}
else
{
lean_object* v_val_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
lean_dec_ref(v_evalsAtAtoms_x27_990_);
lean_dec_ref(v_originalExpr_989_);
v_val_1018_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_993_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_val_1018_);
lean_dec(v___x_993_);
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
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_0interp(lean_interpreter_value* stack)
{
lean_object* v_reified_976_ = stack[0].m_obj;
lean_object* v_a_977_ = stack[1].m_obj;
lean_object* v_a_978_ = stack[2].m_obj;
lean_object* v_a_979_ = stack[3].m_obj;
lean_object* v_a_980_ = stack[4].m_obj;
lean_object* v_a_981_ = stack[5].m_obj;
lean_object* v_a_982_ = stack[6].m_obj;
lean_object* v_a_983_ = stack[7].m_obj;
lean_object* v_a_984_ = stack[8].m_obj;
lean_object* v_a_985_ = stack[9].m_obj;
lean_object* v_a_986_ = stack[10].m_obj;
lean_object* v_a_987_ = stack[11].m_obj;
lean_object* v_res_1026_;
v_res_1026_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(v_reified_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
stack->m_obj
 = v_res_1026_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms___boxed(lean_object* v_reified_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_, lean_object* v_a_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms(v_reified_1027_, v_a_1028_, v_a_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
lean_dec(v_a_1038_);
lean_dec_ref(v_a_1037_);
lean_dec(v_a_1036_);
lean_dec_ref(v_a_1035_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
lean_dec(v_a_1032_);
lean_dec_ref(v_a_1031_);
lean_dec(v_a_1030_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0(lean_object* v_00_u03b2_1041_, lean_object* v_m_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_m_1042_, v_a_1043_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___boxed(lean_object* v_00_u03b2_1045_, lean_object* v_m_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0(v_00_u03b2_1045_, v_m_1046_, v_a_1047_);
lean_dec_ref(v_a_1047_);
lean_dec_ref(v_m_1046_);
return v_res_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1(lean_object* v_00_u03b2_1049_, lean_object* v_m_1050_, lean_object* v_a_1051_, lean_object* v_b_1052_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v_m_1050_, v_a_1051_, v_b_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0(lean_object* v_00_u03b2_1054_, lean_object* v_a_1055_, lean_object* v_x_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___redArg(v_a_1055_, v_x_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1058_, lean_object* v_a_1059_, lean_object* v_x_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0_spec__0(v_00_u03b2_1058_, v_a_1059_, v_x_1060_);
lean_dec(v_x_1060_);
lean_dec_ref(v_a_1059_);
return v_res_1061_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2(lean_object* v_00_u03b2_1062_, lean_object* v_a_1063_, lean_object* v_x_1064_){
_start:
{
uint8_t v___x_1065_; 
v___x_1065_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg(v_a_1063_, v_x_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1063_ = stack[1].m_obj;
lean_object* v_x_1064_ = stack[2].m_obj;
uint8_t v_res_1066_;
v_res_1066_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2(lean_box(0), v_a_1063_, v_x_1064_);
stack->m_num = v_res_1066_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1067_, lean_object* v_a_1068_, lean_object* v_x_1069_){
_start:
{
uint8_t v_res_1070_; lean_object* v_r_1071_; 
v_res_1070_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2(v_00_u03b2_1067_, v_a_1068_, v_x_1069_);
lean_dec(v_x_1069_);
lean_dec_ref(v_a_1068_);
v_r_1071_ = lean_box(v_res_1070_);
return v_r_1071_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3(lean_object* v_00_u03b2_1072_, lean_object* v_data_1073_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3___redArg(v_data_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__4(lean_object* v_00_u03b2_1075_, lean_object* v_a_1076_, lean_object* v_b_1077_, lean_object* v_x_1078_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__4___redArg(v_a_1076_, v_b_1077_, v_x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_1080_, lean_object* v_i_1081_, lean_object* v_source_1082_, lean_object* v_target_1083_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4___redArg(v_i_1081_, v_source_1082_, v_target_1083_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_1085_, lean_object* v_x_1086_, lean_object* v_x_1087_){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__3_spec__4_spec__5___redArg(v_x_1086_, v_x_1087_);
return v___x_1088_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_evalsAtAtoms(lean_object* v_reified_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v_originalExpr_1102_; lean_object* v_evalsAtAtoms_x27_1103_; lean_object* v___x_1104_; lean_object* v_evalsAtCache_1105_; lean_object* v___x_1106_; 
v_originalExpr_1102_ = lean_ctor_get(v_reified_1089_, 1);
lean_inc_ref(v_originalExpr_1102_);
v_evalsAtAtoms_x27_1103_ = lean_ctor_get(v_reified_1089_, 2);
lean_inc_ref(v_evalsAtAtoms_x27_1103_);
lean_dec_ref(v_reified_1089_);
v___x_1104_ = lean_st_ref_get(v_a_1091_);
v_evalsAtCache_1105_ = lean_ctor_get(v___x_1104_, 3);
lean_inc_ref(v_evalsAtCache_1105_);
lean_dec(v___x_1104_);
v___x_1106_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_evalsAtCache_1105_, v_originalExpr_1102_);
lean_dec_ref(v_evalsAtCache_1105_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v___x_1107_; 
lean_inc(v_a_1100_);
lean_inc_ref(v_a_1099_);
lean_inc(v_a_1098_);
lean_inc_ref(v_a_1097_);
lean_inc(v_a_1096_);
lean_inc_ref(v_a_1095_);
lean_inc(v_a_1094_);
lean_inc_ref(v_a_1093_);
lean_inc(v_a_1092_);
lean_inc(v_a_1091_);
lean_inc_ref(v_a_1090_);
v___x_1107_ = lean_apply_12(v_evalsAtAtoms_x27_1103_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, lean_box(0));
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1130_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1110_ = v___x_1107_;
v_isShared_1111_ = v_isSharedCheck_1130_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1107_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1130_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1112_; lean_object* v_atoms_1113_; lean_object* v_atomsAssignmentExprCache_1114_; lean_object* v_atomsAssignmentMapCache_1115_; lean_object* v_evalsAtCache_1116_; lean_object* v_theoryState_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1129_; 
v___x_1112_ = lean_st_ref_take(v_a_1091_);
v_atoms_1113_ = lean_ctor_get(v___x_1112_, 0);
v_atomsAssignmentExprCache_1114_ = lean_ctor_get(v___x_1112_, 1);
v_atomsAssignmentMapCache_1115_ = lean_ctor_get(v___x_1112_, 2);
v_evalsAtCache_1116_ = lean_ctor_get(v___x_1112_, 3);
v_theoryState_1117_ = lean_ctor_get(v___x_1112_, 4);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1119_ = v___x_1112_;
v_isShared_1120_ = v_isSharedCheck_1129_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_theoryState_1117_);
lean_inc(v_evalsAtCache_1116_);
lean_inc(v_atomsAssignmentMapCache_1115_);
lean_inc(v_atomsAssignmentExprCache_1114_);
lean_inc(v_atoms_1113_);
lean_dec(v___x_1112_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1129_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1121_; lean_object* v___x_1123_; 
lean_inc(v_a_1108_);
v___x_1121_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v_evalsAtCache_1116_, v_originalExpr_1102_, v_a_1108_);
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 3, v___x_1121_);
v___x_1123_ = v___x_1119_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_atoms_1113_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v_atomsAssignmentExprCache_1114_);
lean_ctor_set(v_reuseFailAlloc_1128_, 2, v_atomsAssignmentMapCache_1115_);
lean_ctor_set(v_reuseFailAlloc_1128_, 3, v___x_1121_);
lean_ctor_set(v_reuseFailAlloc_1128_, 4, v_theoryState_1117_);
v___x_1123_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
lean_object* v___x_1124_; lean_object* v___x_1126_; 
v___x_1124_ = lean_st_ref_put(v_a_1091_, v___x_1123_);
if (v_isShared_1111_ == 0)
{
v___x_1126_ = v___x_1110_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1108_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
}
else
{
lean_dec_ref(v_originalExpr_1102_);
return v___x_1107_;
}
}
else
{
lean_object* v_val_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec_ref(v_evalsAtAtoms_x27_1103_);
lean_dec_ref(v_originalExpr_1102_);
v_val_1131_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1106_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_val_1131_);
lean_dec(v___x_1106_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
lean_ctor_set_tag(v___x_1133_, 0);
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_val_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_evalsAtAtoms_0interp(lean_interpreter_value* stack)
{
lean_object* v_reified_1089_ = stack[0].m_obj;
lean_object* v_a_1090_ = stack[1].m_obj;
lean_object* v_a_1091_ = stack[2].m_obj;
lean_object* v_a_1092_ = stack[3].m_obj;
lean_object* v_a_1093_ = stack[4].m_obj;
lean_object* v_a_1094_ = stack[5].m_obj;
lean_object* v_a_1095_ = stack[6].m_obj;
lean_object* v_a_1096_ = stack[7].m_obj;
lean_object* v_a_1097_ = stack[8].m_obj;
lean_object* v_a_1098_ = stack[9].m_obj;
lean_object* v_a_1099_ = stack[10].m_obj;
lean_object* v_a_1100_ = stack[11].m_obj;
lean_object* v_res_1139_;
v_res_1139_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_evalsAtAtoms(v_reified_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_);
stack->m_obj
 = v_res_1139_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_evalsAtAtoms___boxed(lean_object* v_reified_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVPred_evalsAtAtoms(v_reified_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
lean_dec(v_a_1151_);
lean_dec_ref(v_a_1150_);
lean_dec(v_a_1149_);
lean_dec_ref(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec(v_a_1142_);
lean_dec_ref(v_a_1141_);
return v_res_1153_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(lean_object* v_reified_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_){
_start:
{
lean_object* v_originalExpr_1167_; lean_object* v_evalsAtAtoms_x27_1168_; lean_object* v___x_1169_; lean_object* v_evalsAtCache_1170_; lean_object* v___x_1171_; 
v_originalExpr_1167_ = lean_ctor_get(v_reified_1154_, 1);
lean_inc_ref(v_originalExpr_1167_);
v_evalsAtAtoms_x27_1168_ = lean_ctor_get(v_reified_1154_, 2);
lean_inc_ref(v_evalsAtAtoms_x27_1168_);
lean_dec_ref(v_reified_1154_);
v___x_1169_ = lean_st_ref_get(v_a_1156_);
v_evalsAtCache_1170_ = lean_ctor_get(v___x_1169_, 3);
lean_inc_ref(v_evalsAtCache_1170_);
lean_dec(v___x_1169_);
v___x_1171_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_evalsAtCache_1170_, v_originalExpr_1167_);
lean_dec_ref(v_evalsAtCache_1170_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v___x_1172_; 
lean_inc(v_a_1165_);
lean_inc_ref(v_a_1164_);
lean_inc(v_a_1163_);
lean_inc_ref(v_a_1162_);
lean_inc(v_a_1161_);
lean_inc_ref(v_a_1160_);
lean_inc(v_a_1159_);
lean_inc_ref(v_a_1158_);
lean_inc(v_a_1157_);
lean_inc(v_a_1156_);
lean_inc_ref(v_a_1155_);
v___x_1172_ = lean_apply_12(v_evalsAtAtoms_x27_1168_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, lean_box(0));
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1195_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1195_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1175_ = v___x_1172_;
v_isShared_1176_ = v_isSharedCheck_1195_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1172_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1195_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1177_; lean_object* v_atoms_1178_; lean_object* v_atomsAssignmentExprCache_1179_; lean_object* v_atomsAssignmentMapCache_1180_; lean_object* v_evalsAtCache_1181_; lean_object* v_theoryState_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1194_; 
v___x_1177_ = lean_st_ref_take(v_a_1156_);
v_atoms_1178_ = lean_ctor_get(v___x_1177_, 0);
v_atomsAssignmentExprCache_1179_ = lean_ctor_get(v___x_1177_, 1);
v_atomsAssignmentMapCache_1180_ = lean_ctor_get(v___x_1177_, 2);
v_evalsAtCache_1181_ = lean_ctor_get(v___x_1177_, 3);
v_theoryState_1182_ = lean_ctor_get(v___x_1177_, 4);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1184_ = v___x_1177_;
v_isShared_1185_ = v_isSharedCheck_1194_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_theoryState_1182_);
lean_inc(v_evalsAtCache_1181_);
lean_inc(v_atomsAssignmentMapCache_1180_);
lean_inc(v_atomsAssignmentExprCache_1179_);
lean_inc(v_atoms_1178_);
lean_dec(v___x_1177_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1194_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; lean_object* v___x_1188_; 
lean_inc(v_a_1173_);
v___x_1186_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v_evalsAtCache_1181_, v_originalExpr_1167_, v_a_1173_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 3, v___x_1186_);
v___x_1188_ = v___x_1184_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_atoms_1178_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_atomsAssignmentExprCache_1179_);
lean_ctor_set(v_reuseFailAlloc_1193_, 2, v_atomsAssignmentMapCache_1180_);
lean_ctor_set(v_reuseFailAlloc_1193_, 3, v___x_1186_);
lean_ctor_set(v_reuseFailAlloc_1193_, 4, v_theoryState_1182_);
v___x_1188_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1189_; lean_object* v___x_1191_; 
v___x_1189_ = lean_st_ref_put(v_a_1156_, v___x_1188_);
if (v_isShared_1176_ == 0)
{
v___x_1191_ = v___x_1175_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1173_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
}
else
{
lean_dec_ref(v_originalExpr_1167_);
return v___x_1172_;
}
}
else
{
lean_object* v_val_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_dec_ref(v_evalsAtAtoms_x27_1168_);
lean_dec_ref(v_originalExpr_1167_);
v_val_1196_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1171_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_val_1196_);
lean_dec(v___x_1171_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
lean_ctor_set_tag(v___x_1198_, 0);
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_val_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms_0interp(lean_interpreter_value* stack)
{
lean_object* v_reified_1154_ = stack[0].m_obj;
lean_object* v_a_1155_ = stack[1].m_obj;
lean_object* v_a_1156_ = stack[2].m_obj;
lean_object* v_a_1157_ = stack[3].m_obj;
lean_object* v_a_1158_ = stack[4].m_obj;
lean_object* v_a_1159_ = stack[5].m_obj;
lean_object* v_a_1160_ = stack[6].m_obj;
lean_object* v_a_1161_ = stack[7].m_obj;
lean_object* v_a_1162_ = stack[8].m_obj;
lean_object* v_a_1163_ = stack[9].m_obj;
lean_object* v_a_1164_ = stack[10].m_obj;
lean_object* v_a_1165_ = stack[11].m_obj;
lean_object* v_res_1204_;
v_res_1204_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(v_reified_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_);
stack->m_obj
 = v_res_1204_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms___boxed(lean_object* v_reified_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lean_Meta_Tactic_BVDecide_ReifiedBVLogical_evalsAtAtoms(v_reified_1205_, v_a_1206_, v_a_1207_, v_a_1208_, v_a_1209_, v_a_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_);
lean_dec(v_a_1216_);
lean_dec_ref(v_a_1215_);
lean_dec(v_a_1214_);
lean_dec_ref(v_a_1213_);
lean_dec(v_a_1212_);
lean_dec_ref(v_a_1211_);
lean_dec(v_a_1210_);
lean_dec_ref(v_a_1209_);
lean_dec(v_a_1208_);
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
return v_res_1218_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_run_spec__0___redArg(size_t v_sz_1219_, size_t v_i_1220_, lean_object* v_bs_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
uint8_t v___x_1229_; 
v___x_1229_ = lean_usize_dec_lt(v_i_1220_, v_sz_1219_);
if (v___x_1229_ == 0)
{
lean_object* v___x_1230_; 
v___x_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1230_, 0, v_bs_1221_);
return v___x_1230_;
}
else
{
lean_object* v_v_1231_; lean_object* v_name_1232_; lean_object* v_type_1233_; lean_object* v_value_1234_; lean_object* v_source_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1258_; 
v_v_1231_ = lean_array_uget(v_bs_1221_, v_i_1220_);
v_name_1232_ = lean_ctor_get(v_v_1231_, 0);
v_type_1233_ = lean_ctor_get(v_v_1231_, 1);
v_value_1234_ = lean_ctor_get(v_v_1231_, 2);
v_source_1235_ = lean_ctor_get(v_v_1231_, 3);
v_isSharedCheck_1258_ = !lean_is_exclusive(v_v_1231_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1237_ = v_v_1231_;
v_isShared_1238_ = v_isSharedCheck_1258_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_source_1235_);
lean_inc(v_value_1234_);
lean_inc(v_type_1233_);
lean_inc(v_name_1232_);
lean_dec(v_v_1231_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1258_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1239_; lean_object* v_bs_x27_1240_; lean_object* v___x_1241_; 
v___x_1239_ = lean_unsigned_to_nat(0u);
v_bs_x27_1240_ = lean_array_uset(v_bs_1221_, v_i_1220_, v___x_1239_);
v___x_1241_ = l_Lean_Meta_Sym_shareCommon(v_type_1233_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1244_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1242_);
lean_dec_ref_known(v___x_1241_, 1);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 1, v_a_1242_);
v___x_1244_ = v___x_1237_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_name_1232_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v_a_1242_);
lean_ctor_set(v_reuseFailAlloc_1249_, 2, v_value_1234_);
lean_ctor_set(v_reuseFailAlloc_1249_, 3, v_source_1235_);
v___x_1244_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
size_t v___x_1245_; size_t v___x_1246_; lean_object* v___x_1247_; 
v___x_1245_ = ((size_t)1ULL);
v___x_1246_ = lean_usize_add(v_i_1220_, v___x_1245_);
v___x_1247_ = lean_array_uset(v_bs_x27_1240_, v_i_1220_, v___x_1244_);
v_i_1220_ = v___x_1246_;
v_bs_1221_ = v___x_1247_;
goto _start;
}
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec_ref(v_bs_x27_1240_);
lean_del_object(v___x_1237_);
lean_dec(v_source_1235_);
lean_dec_ref(v_value_1234_);
lean_dec(v_name_1232_);
v_a_1250_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1241_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1241_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_run_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1219_ = stack[0].m_num;
size_t v_i_1220_ = stack[1].m_num;
lean_object* v_bs_1221_ = stack[2].m_obj;
lean_object* v___y_1222_ = stack[3].m_obj;
lean_object* v___y_1223_ = stack[4].m_obj;
lean_object* v___y_1224_ = stack[5].m_obj;
lean_object* v___y_1225_ = stack[6].m_obj;
lean_object* v___y_1226_ = stack[7].m_obj;
lean_object* v___y_1227_ = stack[8].m_obj;
lean_object* v_res_1259_;
v_res_1259_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_run_spec__0___redArg(v_sz_1219_, v_i_1220_, v_bs_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
stack->m_obj
 = v_res_1259_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_run_spec__0___redArg___boxed(lean_object* v_sz_1260_, lean_object* v_i_1261_, lean_object* v_bs_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
size_t v_sz_boxed_1270_; size_t v_i_boxed_1271_; lean_object* v_res_1272_; 
v_sz_boxed_1270_ = lean_unbox_usize(v_sz_1260_);
lean_dec(v_sz_1260_);
v_i_boxed_1271_ = lean_unbox_usize(v_i_1261_);
lean_dec(v_i_1261_);
v_res_1272_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_run_spec__0___redArg(v_sz_boxed_1270_, v_i_boxed_1271_, v_bs_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
return v_res_1272_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1273_ = lean_box(0);
v___x_1274_ = lean_unsigned_to_nat(16u);
v___x_1275_ = lean_mk_array(v___x_1274_, v___x_1273_);
return v___x_1275_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1276_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__0, &l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__0_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__0);
v___x_1277_ = lean_unsigned_to_nat(0u);
v___x_1278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
lean_ctor_set(v___x_1278_, 1, v___x_1276_);
return v___x_1278_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__4(void){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1283_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__3));
v___x_1284_ = lean_box(0);
v___x_1285_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__1);
v___x_1286_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1285_);
lean_ctor_set(v___x_1286_, 1, v___x_1284_);
lean_ctor_set(v___x_1286_, 2, v___x_1284_);
lean_ctor_set(v___x_1286_, 3, v___x_1285_);
lean_ctor_set(v___x_1286_, 4, v___x_1283_);
return v___x_1286_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg(lean_object* v_m_1287_, lean_object* v_hypotheses_1288_, lean_object* v_cfg_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
size_t v_sz_1300_; size_t v___x_1301_; lean_object* v___x_1302_; 
v_sz_1300_ = lean_array_size(v_hypotheses_1288_);
v___x_1301_ = ((size_t)0ULL);
v___x_1302_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_run_spec__0___redArg(v_sz_1300_, v___x_1301_, v_hypotheses_1288_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_object* v_a_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_a_1303_);
lean_dec_ref_known(v___x_1302_, 1);
v___x_1304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1304_, 0, v_a_1303_);
lean_ctor_set(v___x_1304_, 1, v_cfg_1289_);
v___x_1305_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__4, &l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__4_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__4);
v___x_1306_ = lean_st_mk_ref(v___x_1305_);
lean_inc(v_a_1298_);
lean_inc_ref(v_a_1297_);
lean_inc(v_a_1296_);
lean_inc_ref(v_a_1295_);
lean_inc(v_a_1294_);
lean_inc_ref(v_a_1293_);
lean_inc(v_a_1292_);
lean_inc_ref(v_a_1291_);
lean_inc(v_a_1290_);
lean_inc(v___x_1306_);
v___x_1307_ = lean_apply_12(v_m_1287_, v___x_1304_, v___x_1306_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, lean_box(0));
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1316_; 
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1310_ = v___x_1307_;
v_isShared_1311_ = v_isSharedCheck_1316_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1307_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1316_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1312_ = lean_st_ref_get(v___x_1306_);
lean_dec(v___x_1306_);
lean_dec(v___x_1312_);
if (v_isShared_1311_ == 0)
{
v___x_1314_ = v___x_1310_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1308_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
else
{
lean_dec(v___x_1306_);
return v___x_1307_;
}
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_dec_ref(v_cfg_1289_);
lean_dec_ref(v_m_1287_);
v_a_1317_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1302_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1302_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1287_ = stack[0].m_obj;
lean_object* v_hypotheses_1288_ = stack[1].m_obj;
lean_object* v_cfg_1289_ = stack[2].m_obj;
lean_object* v_a_1290_ = stack[3].m_obj;
lean_object* v_a_1291_ = stack[4].m_obj;
lean_object* v_a_1292_ = stack[5].m_obj;
lean_object* v_a_1293_ = stack[6].m_obj;
lean_object* v_a_1294_ = stack[7].m_obj;
lean_object* v_a_1295_ = stack[8].m_obj;
lean_object* v_a_1296_ = stack[9].m_obj;
lean_object* v_a_1297_ = stack[10].m_obj;
lean_object* v_a_1298_ = stack[11].m_obj;
lean_object* v_res_1325_;
v_res_1325_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg(v_m_1287_, v_hypotheses_1288_, v_cfg_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_);
stack->m_obj
 = v_res_1325_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___boxed(lean_object* v_m_1326_, lean_object* v_hypotheses_1327_, lean_object* v_cfg_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg(v_m_1326_, v_hypotheses_1327_, v_cfg_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_);
lean_dec(v_a_1337_);
lean_dec_ref(v_a_1336_);
lean_dec(v_a_1335_);
lean_dec_ref(v_a_1334_);
lean_dec(v_a_1333_);
lean_dec_ref(v_a_1332_);
lean_dec(v_a_1331_);
lean_dec_ref(v_a_1330_);
lean_dec(v_a_1329_);
return v_res_1339_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_run(lean_object* v_00_u03b1_1340_, lean_object* v_m_1341_, lean_object* v_hypotheses_1342_, lean_object* v_cfg_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg(v_m_1341_, v_hypotheses_1342_, v_cfg_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
return v___x_1354_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_ReifyM_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1341_ = stack[1].m_obj;
lean_object* v_hypotheses_1342_ = stack[2].m_obj;
lean_object* v_cfg_1343_ = stack[3].m_obj;
lean_object* v_a_1344_ = stack[4].m_obj;
lean_object* v_a_1345_ = stack[5].m_obj;
lean_object* v_a_1346_ = stack[6].m_obj;
lean_object* v_a_1347_ = stack[7].m_obj;
lean_object* v_a_1348_ = stack[8].m_obj;
lean_object* v_a_1349_ = stack[9].m_obj;
lean_object* v_a_1350_ = stack[10].m_obj;
lean_object* v_a_1351_ = stack[11].m_obj;
lean_object* v_a_1352_ = stack[12].m_obj;
lean_object* v_res_1355_;
v_res_1355_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_run(lean_box(0), v_m_1341_, v_hypotheses_1342_, v_cfg_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
stack->m_obj
 = v_res_1355_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_run___boxed(lean_object* v_00_u03b1_1356_, lean_object* v_m_1357_, lean_object* v_hypotheses_1358_, lean_object* v_cfg_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_run(v_00_u03b1_1356_, v_m_1357_, v_hypotheses_1358_, v_cfg_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
lean_dec(v_a_1364_);
lean_dec_ref(v_a_1363_);
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
lean_dec(v_a_1360_);
return v_res_1370_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_run_spec__0(size_t v_sz_1371_, size_t v_i_1372_, lean_object* v_bs_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_run_spec__0___redArg(v_sz_1371_, v_i_1372_, v_bs_1373_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
return v___x_1384_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_run_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1371_ = stack[0].m_num;
size_t v_i_1372_ = stack[1].m_num;
lean_object* v_bs_1373_ = stack[2].m_obj;
lean_object* v___y_1374_ = stack[3].m_obj;
lean_object* v___y_1375_ = stack[4].m_obj;
lean_object* v___y_1376_ = stack[5].m_obj;
lean_object* v___y_1377_ = stack[6].m_obj;
lean_object* v___y_1378_ = stack[7].m_obj;
lean_object* v___y_1379_ = stack[8].m_obj;
lean_object* v___y_1380_ = stack[9].m_obj;
lean_object* v___y_1381_ = stack[10].m_obj;
lean_object* v___y_1382_ = stack[11].m_obj;
lean_object* v_res_1385_;
v_res_1385_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_run_spec__0(v_sz_1371_, v_i_1372_, v_bs_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
stack->m_obj
 = v_res_1385_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_run_spec__0___boxed(lean_object* v_sz_1386_, lean_object* v_i_1387_, lean_object* v_bs_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
size_t v_sz_boxed_1399_; size_t v_i_boxed_1400_; lean_object* v_res_1401_; 
v_sz_boxed_1399_ = lean_unbox_usize(v_sz_1386_);
lean_dec(v_sz_1386_);
v_i_boxed_1400_ = lean_unbox_usize(v_i_1387_);
lean_dec(v_i_1387_);
v_res_1401_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_run_spec__0(v_sz_boxed_1399_, v_i_boxed_1400_, v_bs_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__2(lean_object* v_x_1402_, lean_object* v_x_1403_){
_start:
{
if (lean_obj_tag(v_x_1403_) == 0)
{
return v_x_1402_;
}
else
{
lean_object* v_key_1404_; lean_object* v_value_1405_; lean_object* v_tail_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v_key_1404_ = lean_ctor_get(v_x_1403_, 0);
v_value_1405_ = lean_ctor_get(v_x_1403_, 1);
v_tail_1406_ = lean_ctor_get(v_x_1403_, 2);
lean_inc(v_value_1405_);
lean_inc(v_key_1404_);
v___x_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1407_, 0, v_key_1404_);
lean_ctor_set(v___x_1407_, 1, v_value_1405_);
v___x_1408_ = lean_array_push(v_x_1402_, v___x_1407_);
v_x_1402_ = v___x_1408_;
v_x_1403_ = v_tail_1406_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__2___boxed(lean_object* v_x_1410_, lean_object* v_x_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__2(v_x_1410_, v_x_1411_);
lean_dec(v_x_1411_);
return v_res_1412_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__3(lean_object* v_as_1413_, size_t v_i_1414_, size_t v_stop_1415_, lean_object* v_b_1416_){
_start:
{
uint8_t v___x_1417_; 
v___x_1417_ = lean_usize_dec_eq(v_i_1414_, v_stop_1415_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; lean_object* v___x_1419_; size_t v___x_1420_; size_t v___x_1421_; 
v___x_1418_ = lean_array_uget_borrowed(v_as_1413_, v_i_1414_);
v___x_1419_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__2(v_b_1416_, v___x_1418_);
v___x_1420_ = ((size_t)1ULL);
v___x_1421_ = lean_usize_add(v_i_1414_, v___x_1420_);
v_i_1414_ = v___x_1421_;
v_b_1416_ = v___x_1419_;
goto _start;
}
else
{
return v_b_1416_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1413_ = stack[0].m_obj;
size_t v_i_1414_ = stack[1].m_num;
size_t v_stop_1415_ = stack[2].m_num;
lean_object* v_b_1416_ = stack[3].m_obj;
lean_object* v_res_1423_;
v_res_1423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__3(v_as_1413_, v_i_1414_, v_stop_1415_, v_b_1416_);
stack->m_obj
 = v_res_1423_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__3___boxed(lean_object* v_as_1424_, lean_object* v_i_1425_, lean_object* v_stop_1426_, lean_object* v_b_1427_){
_start:
{
size_t v_i_boxed_1428_; size_t v_stop_boxed_1429_; lean_object* v_res_1430_; 
v_i_boxed_1428_ = lean_unbox_usize(v_i_1425_);
lean_dec(v_i_1425_);
v_stop_boxed_1429_ = lean_unbox_usize(v_stop_1426_);
lean_dec(v_stop_1426_);
v_res_1430_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__3(v_as_1424_, v_i_boxed_1428_, v_stop_boxed_1429_, v_b_1427_);
lean_dec_ref(v_as_1424_);
return v_res_1430_;
}
}
uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___redArg___lam__0(lean_object* v_x1_1431_, lean_object* v_x2_1432_){
_start:
{
lean_object* v_snd_1433_; lean_object* v_snd_1434_; lean_object* v_atomNumber_1435_; lean_object* v_atomNumber_1436_; uint8_t v___x_1437_; 
v_snd_1433_ = lean_ctor_get(v_x1_1431_, 1);
v_snd_1434_ = lean_ctor_get(v_x2_1432_, 1);
v_atomNumber_1435_ = lean_ctor_get(v_snd_1433_, 1);
v_atomNumber_1436_ = lean_ctor_get(v_snd_1434_, 1);
v___x_1437_ = lean_nat_dec_lt(v_atomNumber_1435_, v_atomNumber_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x1_1431_ = stack[0].m_obj;
lean_object* v_x2_1432_ = stack[1].m_obj;
uint8_t v_res_1438_;
v_res_1438_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___redArg___lam__0(v_x1_1431_, v_x2_1432_);
stack->m_num = v_res_1438_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___redArg___lam__0___boxed(lean_object* v_x1_1439_, lean_object* v_x2_1440_){
_start:
{
uint8_t v_res_1441_; lean_object* v_r_1442_; 
v_res_1441_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___redArg___lam__0(v_x1_1439_, v_x2_1440_);
lean_dec_ref(v_x2_1440_);
lean_dec_ref(v_x1_1439_);
v_r_1442_ = lean_box(v_res_1441_);
return v_r_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1_spec__1___redArg(lean_object* v_hi_1443_, lean_object* v_pivot_1444_, lean_object* v_as_1445_, lean_object* v_i_1446_, lean_object* v_k_1447_){
_start:
{
uint8_t v___x_1448_; 
v___x_1448_ = lean_nat_dec_lt(v_k_1447_, v_hi_1443_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
lean_dec(v_k_1447_);
v___x_1449_ = lean_array_fswap(v_as_1445_, v_i_1446_, v_hi_1443_);
v___x_1450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1450_, 0, v_i_1446_);
lean_ctor_set(v___x_1450_, 1, v___x_1449_);
return v___x_1450_;
}
else
{
lean_object* v___x_1451_; lean_object* v_snd_1452_; lean_object* v_snd_1453_; lean_object* v_atomNumber_1454_; lean_object* v_atomNumber_1455_; uint8_t v___x_1456_; 
v___x_1451_ = lean_array_fget_borrowed(v_as_1445_, v_k_1447_);
v_snd_1452_ = lean_ctor_get(v___x_1451_, 1);
v_snd_1453_ = lean_ctor_get(v_pivot_1444_, 1);
v_atomNumber_1454_ = lean_ctor_get(v_snd_1452_, 1);
v_atomNumber_1455_ = lean_ctor_get(v_snd_1453_, 1);
v___x_1456_ = lean_nat_dec_lt(v_atomNumber_1454_, v_atomNumber_1455_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1457_ = lean_unsigned_to_nat(1u);
v___x_1458_ = lean_nat_add(v_k_1447_, v___x_1457_);
lean_dec(v_k_1447_);
v_k_1447_ = v___x_1458_;
goto _start;
}
else
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1460_ = lean_array_fswap(v_as_1445_, v_i_1446_, v_k_1447_);
v___x_1461_ = lean_unsigned_to_nat(1u);
v___x_1462_ = lean_nat_add(v_i_1446_, v___x_1461_);
lean_dec(v_i_1446_);
v___x_1463_ = lean_nat_add(v_k_1447_, v___x_1461_);
lean_dec(v_k_1447_);
v_as_1445_ = v___x_1460_;
v_i_1446_ = v___x_1462_;
v_k_1447_ = v___x_1463_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1_spec__1___redArg___boxed(lean_object* v_hi_1465_, lean_object* v_pivot_1466_, lean_object* v_as_1467_, lean_object* v_i_1468_, lean_object* v_k_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1_spec__1___redArg(v_hi_1465_, v_pivot_1466_, v_as_1467_, v_i_1468_, v_k_1469_);
lean_dec_ref(v_pivot_1466_);
lean_dec(v_hi_1465_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___redArg(lean_object* v_n_1471_, lean_object* v_as_1472_, lean_object* v_lo_1473_, lean_object* v_hi_1474_){
_start:
{
lean_object* v___y_1476_; uint8_t v___x_1486_; 
v___x_1486_ = lean_nat_dec_lt(v_lo_1473_, v_hi_1474_);
if (v___x_1486_ == 0)
{
lean_dec(v_lo_1473_);
return v_as_1472_;
}
else
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v_mid_1489_; lean_object* v___y_1491_; lean_object* v___y_1497_; lean_object* v___x_1502_; lean_object* v___x_1503_; uint8_t v___x_1504_; 
v___x_1487_ = lean_nat_add(v_lo_1473_, v_hi_1474_);
v___x_1488_ = lean_unsigned_to_nat(1u);
v_mid_1489_ = lean_nat_shiftr(v___x_1487_, v___x_1488_);
lean_dec(v___x_1487_);
v___x_1502_ = lean_array_fget_borrowed(v_as_1472_, v_mid_1489_);
v___x_1503_ = lean_array_fget_borrowed(v_as_1472_, v_lo_1473_);
v___x_1504_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___redArg___lam__0(v___x_1502_, v___x_1503_);
if (v___x_1504_ == 0)
{
v___y_1497_ = v_as_1472_;
goto v___jp_1496_;
}
else
{
lean_object* v___x_1505_; 
v___x_1505_ = lean_array_fswap(v_as_1472_, v_lo_1473_, v_mid_1489_);
v___y_1497_ = v___x_1505_;
goto v___jp_1496_;
}
v___jp_1490_:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; uint8_t v___x_1494_; 
v___x_1492_ = lean_array_fget_borrowed(v___y_1491_, v_mid_1489_);
v___x_1493_ = lean_array_fget_borrowed(v___y_1491_, v_hi_1474_);
v___x_1494_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___redArg___lam__0(v___x_1492_, v___x_1493_);
if (v___x_1494_ == 0)
{
lean_dec(v_mid_1489_);
v___y_1476_ = v___y_1491_;
goto v___jp_1475_;
}
else
{
lean_object* v___x_1495_; 
v___x_1495_ = lean_array_fswap(v___y_1491_, v_mid_1489_, v_hi_1474_);
lean_dec(v_mid_1489_);
v___y_1476_ = v___x_1495_;
goto v___jp_1475_;
}
}
v___jp_1496_:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; uint8_t v___x_1500_; 
v___x_1498_ = lean_array_fget_borrowed(v___y_1497_, v_hi_1474_);
v___x_1499_ = lean_array_fget_borrowed(v___y_1497_, v_lo_1473_);
v___x_1500_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___redArg___lam__0(v___x_1498_, v___x_1499_);
if (v___x_1500_ == 0)
{
v___y_1491_ = v___y_1497_;
goto v___jp_1490_;
}
else
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_array_fswap(v___y_1497_, v_lo_1473_, v_hi_1474_);
v___y_1491_ = v___x_1501_;
goto v___jp_1490_;
}
}
}
v___jp_1475_:
{
lean_object* v_pivot_1477_; lean_object* v___x_1478_; lean_object* v_fst_1479_; lean_object* v_snd_1480_; uint8_t v___x_1481_; 
v_pivot_1477_ = lean_array_fget(v___y_1476_, v_hi_1474_);
lean_inc_n(v_lo_1473_, 2);
v___x_1478_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1_spec__1___redArg(v_hi_1474_, v_pivot_1477_, v___y_1476_, v_lo_1473_, v_lo_1473_);
lean_dec(v_pivot_1477_);
v_fst_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_fst_1479_);
v_snd_1480_ = lean_ctor_get(v___x_1478_, 1);
lean_inc(v_snd_1480_);
lean_dec_ref(v___x_1478_);
v___x_1481_ = lean_nat_dec_le(v_hi_1474_, v_fst_1479_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1482_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___redArg(v_n_1471_, v_snd_1480_, v_lo_1473_, v_fst_1479_);
v___x_1483_ = lean_unsigned_to_nat(1u);
v___x_1484_ = lean_nat_add(v_fst_1479_, v___x_1483_);
lean_dec(v_fst_1479_);
v_as_1472_ = v___x_1482_;
v_lo_1473_ = v___x_1484_;
goto _start;
}
else
{
lean_dec(v_fst_1479_);
lean_dec(v_lo_1473_);
return v_snd_1480_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___redArg___boxed(lean_object* v_n_1506_, lean_object* v_as_1507_, lean_object* v_lo_1508_, lean_object* v_hi_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___redArg(v_n_1506_, v_as_1507_, v_lo_1508_, v_hi_1509_);
lean_dec(v_hi_1509_);
lean_dec(v_n_1506_);
return v_res_1510_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__0(size_t v_sz_1511_, size_t v_i_1512_, lean_object* v_bs_1513_){
_start:
{
uint8_t v___x_1514_; 
v___x_1514_ = lean_usize_dec_lt(v_i_1512_, v_sz_1511_);
if (v___x_1514_ == 0)
{
return v_bs_1513_;
}
else
{
lean_object* v_v_1515_; lean_object* v_snd_1516_; lean_object* v_fst_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1531_; 
v_v_1515_ = lean_array_uget(v_bs_1513_, v_i_1512_);
v_snd_1516_ = lean_ctor_get(v_v_1515_, 1);
v_fst_1517_ = lean_ctor_get(v_v_1515_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_v_1515_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1519_ = v_v_1515_;
v_isShared_1520_ = v_isSharedCheck_1531_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_snd_1516_);
lean_inc(v_fst_1517_);
lean_dec(v_v_1515_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1531_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v_width_1521_; lean_object* v___x_1522_; lean_object* v_bs_x27_1523_; lean_object* v___x_1525_; 
v_width_1521_ = lean_ctor_get(v_snd_1516_, 0);
lean_inc(v_width_1521_);
lean_dec(v_snd_1516_);
v___x_1522_ = lean_unsigned_to_nat(0u);
v_bs_x27_1523_ = lean_array_uset(v_bs_1513_, v_i_1512_, v___x_1522_);
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 1, v_fst_1517_);
lean_ctor_set(v___x_1519_, 0, v_width_1521_);
v___x_1525_ = v___x_1519_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_width_1521_);
lean_ctor_set(v_reuseFailAlloc_1530_, 1, v_fst_1517_);
v___x_1525_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
size_t v___x_1526_; size_t v___x_1527_; lean_object* v___x_1528_; 
v___x_1526_ = ((size_t)1ULL);
v___x_1527_ = lean_usize_add(v_i_1512_, v___x_1526_);
v___x_1528_ = lean_array_uset(v_bs_x27_1523_, v_i_1512_, v___x_1525_);
v_i_1512_ = v___x_1527_;
v_bs_1513_ = v___x_1528_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1511_ = stack[0].m_num;
size_t v_i_1512_ = stack[1].m_num;
lean_object* v_bs_1513_ = stack[2].m_obj;
lean_object* v_res_1532_;
v_res_1532_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__0(v_sz_1511_, v_i_1512_, v_bs_1513_);
stack->m_obj
 = v_res_1532_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__0___boxed(lean_object* v_sz_1533_, lean_object* v_i_1534_, lean_object* v_bs_1535_){
_start:
{
size_t v_sz_boxed_1536_; size_t v_i_boxed_1537_; lean_object* v_res_1538_; 
v_sz_boxed_1536_ = lean_unbox_usize(v_sz_1533_);
lean_dec(v_sz_1533_);
v_i_boxed_1537_ = lean_unbox_usize(v_i_1534_);
lean_dec(v_i_1534_);
v_res_1538_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__0(v_sz_boxed_1536_, v_i_boxed_1537_, v_bs_1535_);
return v_res_1538_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atoms___redArg(lean_object* v_a_1539_){
_start:
{
lean_object* v___x_1541_; lean_object* v___y_1543_; lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___y_1558_; lean_object* v___y_1561_; lean_object* v_atoms_1568_; lean_object* v_size_1569_; lean_object* v_buckets_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; uint8_t v___x_1574_; 
v___x_1541_ = lean_st_ref_get(v_a_1539_);
v_atoms_1568_ = lean_ctor_get(v___x_1541_, 0);
lean_inc_ref(v_atoms_1568_);
lean_dec(v___x_1541_);
v_size_1569_ = lean_ctor_get(v_atoms_1568_, 0);
lean_inc(v_size_1569_);
v_buckets_1570_ = lean_ctor_get(v_atoms_1568_, 1);
lean_inc_ref(v_buckets_1570_);
lean_dec_ref(v_atoms_1568_);
v___x_1571_ = lean_mk_empty_array_with_capacity(v_size_1569_);
lean_dec(v_size_1569_);
v___x_1572_ = lean_unsigned_to_nat(0u);
v___x_1573_ = lean_array_get_size(v_buckets_1570_);
v___x_1574_ = lean_nat_dec_lt(v___x_1572_, v___x_1573_);
if (v___x_1574_ == 0)
{
lean_dec_ref(v_buckets_1570_);
v___y_1561_ = v___x_1571_;
goto v___jp_1560_;
}
else
{
size_t v___x_1575_; size_t v___x_1576_; lean_object* v___x_1577_; 
v___x_1575_ = ((size_t)0ULL);
v___x_1576_ = lean_usize_of_nat(v___x_1573_);
v___x_1577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__3(v_buckets_1570_, v___x_1575_, v___x_1576_, v___x_1571_);
lean_dec_ref(v_buckets_1570_);
v___y_1561_ = v___x_1577_;
goto v___jp_1560_;
}
v___jp_1542_:
{
size_t v_sz_1544_; size_t v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v_sz_1544_ = lean_array_size(v___y_1543_);
v___x_1545_ = ((size_t)0ULL);
v___x_1546_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__0(v_sz_1544_, v___x_1545_, v___y_1543_);
v___x_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
return v___x_1547_;
}
v___jp_1548_:
{
lean_object* v___x_1553_; 
v___x_1553_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___redArg(v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
lean_dec(v___y_1552_);
lean_dec(v___y_1549_);
v___y_1543_ = v___x_1553_;
goto v___jp_1542_;
}
v___jp_1554_:
{
uint8_t v___x_1559_; 
v___x_1559_ = lean_nat_dec_le(v___y_1558_, v___y_1557_);
if (v___x_1559_ == 0)
{
lean_dec(v___y_1557_);
lean_inc(v___y_1558_);
v___y_1549_ = v___y_1555_;
v___y_1550_ = v___y_1556_;
v___y_1551_ = v___y_1558_;
v___y_1552_ = v___y_1558_;
goto v___jp_1548_;
}
else
{
v___y_1549_ = v___y_1555_;
v___y_1550_ = v___y_1556_;
v___y_1551_ = v___y_1558_;
v___y_1552_ = v___y_1557_;
goto v___jp_1548_;
}
}
v___jp_1560_:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
v___x_1562_ = lean_array_get_size(v___y_1561_);
v___x_1563_ = lean_unsigned_to_nat(0u);
v___x_1564_ = lean_nat_dec_eq(v___x_1562_, v___x_1563_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; lean_object* v___x_1566_; uint8_t v___x_1567_; 
v___x_1565_ = lean_unsigned_to_nat(1u);
v___x_1566_ = lean_nat_sub(v___x_1562_, v___x_1565_);
v___x_1567_ = lean_nat_dec_le(v___x_1563_, v___x_1566_);
if (v___x_1567_ == 0)
{
lean_inc(v___x_1566_);
v___y_1555_ = v___x_1562_;
v___y_1556_ = v___y_1561_;
v___y_1557_ = v___x_1566_;
v___y_1558_ = v___x_1566_;
goto v___jp_1554_;
}
else
{
v___y_1555_ = v___x_1562_;
v___y_1556_ = v___y_1561_;
v___y_1557_ = v___x_1566_;
v___y_1558_ = v___x_1563_;
goto v___jp_1554_;
}
}
else
{
v___y_1543_ = v___y_1561_;
goto v___jp_1542_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_ReifyM_atoms___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1539_ = stack[0].m_obj;
lean_object* v_res_1578_;
v_res_1578_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atoms___redArg(v_a_1539_);
stack->m_obj
 = v_res_1578_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atoms___redArg___boxed(lean_object* v_a_1579_, lean_object* v_a_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atoms___redArg(v_a_1579_);
lean_dec(v_a_1579_);
return v_res_1581_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atoms(lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atoms___redArg(v_a_1583_);
return v___x_1594_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_ReifyM_atoms_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1582_ = stack[0].m_obj;
lean_object* v_a_1583_ = stack[1].m_obj;
lean_object* v_a_1584_ = stack[2].m_obj;
lean_object* v_a_1585_ = stack[3].m_obj;
lean_object* v_a_1586_ = stack[4].m_obj;
lean_object* v_a_1587_ = stack[5].m_obj;
lean_object* v_a_1588_ = stack[6].m_obj;
lean_object* v_a_1589_ = stack[7].m_obj;
lean_object* v_a_1590_ = stack[8].m_obj;
lean_object* v_a_1591_ = stack[9].m_obj;
lean_object* v_a_1592_ = stack[10].m_obj;
lean_object* v_res_1595_;
v_res_1595_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atoms(v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_);
stack->m_obj
 = v_res_1595_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atoms___boxed(lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atoms(v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
lean_dec(v_a_1606_);
lean_dec_ref(v_a_1605_);
lean_dec(v_a_1604_);
lean_dec_ref(v_a_1603_);
lean_dec(v_a_1602_);
lean_dec_ref(v_a_1601_);
lean_dec(v_a_1600_);
lean_dec_ref(v_a_1599_);
lean_dec(v_a_1598_);
lean_dec(v_a_1597_);
lean_dec_ref(v_a_1596_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1(lean_object* v_n_1609_, lean_object* v_as_1610_, lean_object* v_lo_1611_, lean_object* v_hi_1612_, lean_object* v_w_1613_, lean_object* v_hlo_1614_, lean_object* v_hhi_1615_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___redArg(v_n_1609_, v_as_1610_, v_lo_1611_, v_hi_1612_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1___boxed(lean_object* v_n_1617_, lean_object* v_as_1618_, lean_object* v_lo_1619_, lean_object* v_hi_1620_, lean_object* v_w_1621_, lean_object* v_hlo_1622_, lean_object* v_hhi_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1(v_n_1617_, v_as_1618_, v_lo_1619_, v_hi_1620_, v_w_1621_, v_hlo_1622_, v_hhi_1623_);
lean_dec(v_hi_1620_);
lean_dec(v_n_1617_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1_spec__1(lean_object* v_n_1625_, lean_object* v_lo_1626_, lean_object* v_hi_1627_, lean_object* v_hhi_1628_, lean_object* v_pivot_1629_, lean_object* v_as_1630_, lean_object* v_i_1631_, lean_object* v_k_1632_, lean_object* v_ilo_1633_, lean_object* v_ik_1634_, lean_object* v_w_1635_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1_spec__1___redArg(v_hi_1627_, v_pivot_1629_, v_as_1630_, v_i_1631_, v_k_1632_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1_spec__1___boxed(lean_object* v_n_1637_, lean_object* v_lo_1638_, lean_object* v_hi_1639_, lean_object* v_hhi_1640_, lean_object* v_pivot_1641_, lean_object* v_as_1642_, lean_object* v_i_1643_, lean_object* v_k_1644_, lean_object* v_ilo_1645_, lean_object* v_ik_1646_, lean_object* v_w_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Meta_Tactic_BVDecide_ReifyM_atoms_spec__1_spec__1(v_n_1637_, v_lo_1638_, v_hi_1639_, v_hhi_1640_, v_pivot_1641_, v_as_1642_, v_i_1643_, v_k_1644_, v_ilo_1645_, v_ik_1646_, v_w_1647_);
lean_dec_ref(v_pivot_1641_);
lean_dec(v_hi_1639_);
lean_dec(v_lo_1638_);
lean_dec(v_n_1637_);
return v_res_1648_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__2___redArg(lean_object* v_a_1649_, lean_object* v_x_1650_){
_start:
{
if (lean_obj_tag(v_x_1650_) == 0)
{
uint8_t v___x_1651_; 
v___x_1651_ = 0;
return v___x_1651_;
}
else
{
lean_object* v_key_1652_; lean_object* v_tail_1653_; uint8_t v___x_1654_; 
v_key_1652_ = lean_ctor_get(v_x_1650_, 0);
v_tail_1653_ = lean_ctor_get(v_x_1650_, 2);
v___x_1654_ = lean_nat_dec_eq(v_key_1652_, v_a_1649_);
if (v___x_1654_ == 0)
{
v_x_1650_ = v_tail_1653_;
goto _start;
}
else
{
return v___x_1654_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1649_ = stack[0].m_obj;
lean_object* v_x_1650_ = stack[1].m_obj;
uint8_t v_res_1656_;
v_res_1656_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__2___redArg(v_a_1649_, v_x_1650_);
stack->m_num = v_res_1656_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_a_1657_, lean_object* v_x_1658_){
_start:
{
uint8_t v_res_1659_; lean_object* v_r_1660_; 
v_res_1659_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__2___redArg(v_a_1657_, v_x_1658_);
lean_dec(v_x_1658_);
lean_dec(v_a_1657_);
v_r_1660_ = lean_box(v_res_1659_);
return v_r_1660_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__4___redArg(lean_object* v_a_1661_, lean_object* v_b_1662_, lean_object* v_x_1663_){
_start:
{
if (lean_obj_tag(v_x_1663_) == 0)
{
lean_dec(v_b_1662_);
lean_dec(v_a_1661_);
return v_x_1663_;
}
else
{
lean_object* v_key_1664_; lean_object* v_value_1665_; lean_object* v_tail_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1678_; 
v_key_1664_ = lean_ctor_get(v_x_1663_, 0);
v_value_1665_ = lean_ctor_get(v_x_1663_, 1);
v_tail_1666_ = lean_ctor_get(v_x_1663_, 2);
v_isSharedCheck_1678_ = !lean_is_exclusive(v_x_1663_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1668_ = v_x_1663_;
v_isShared_1669_ = v_isSharedCheck_1678_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_tail_1666_);
lean_inc(v_value_1665_);
lean_inc(v_key_1664_);
lean_dec(v_x_1663_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1678_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
uint8_t v___x_1670_; 
v___x_1670_ = lean_nat_dec_eq(v_key_1664_, v_a_1661_);
if (v___x_1670_ == 0)
{
lean_object* v___x_1671_; lean_object* v___x_1673_; 
v___x_1671_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__4___redArg(v_a_1661_, v_b_1662_, v_tail_1666_);
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 2, v___x_1671_);
v___x_1673_ = v___x_1668_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_key_1664_);
lean_ctor_set(v_reuseFailAlloc_1674_, 1, v_value_1665_);
lean_ctor_set(v_reuseFailAlloc_1674_, 2, v___x_1671_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
else
{
lean_object* v___x_1676_; 
lean_dec(v_value_1665_);
lean_dec(v_key_1664_);
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 1, v_b_1662_);
lean_ctor_set(v___x_1668_, 0, v_a_1661_);
v___x_1676_ = v___x_1668_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1661_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v_b_1662_);
lean_ctor_set(v_reuseFailAlloc_1677_, 2, v_tail_1666_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__3_spec__6_spec__8___redArg(lean_object* v_x_1679_, lean_object* v_x_1680_){
_start:
{
if (lean_obj_tag(v_x_1680_) == 0)
{
return v_x_1679_;
}
else
{
lean_object* v_key_1681_; lean_object* v_value_1682_; lean_object* v_tail_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1706_; 
v_key_1681_ = lean_ctor_get(v_x_1680_, 0);
v_value_1682_ = lean_ctor_get(v_x_1680_, 1);
v_tail_1683_ = lean_ctor_get(v_x_1680_, 2);
v_isSharedCheck_1706_ = !lean_is_exclusive(v_x_1680_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1685_ = v_x_1680_;
v_isShared_1686_ = v_isSharedCheck_1706_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_tail_1683_);
lean_inc(v_value_1682_);
lean_inc(v_key_1681_);
lean_dec(v_x_1680_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1706_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1687_; uint64_t v___x_1688_; uint64_t v___x_1689_; uint64_t v___x_1690_; uint64_t v_fold_1691_; uint64_t v___x_1692_; uint64_t v___x_1693_; uint64_t v___x_1694_; size_t v___x_1695_; size_t v___x_1696_; size_t v___x_1697_; size_t v___x_1698_; size_t v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1702_; 
v___x_1687_ = lean_array_get_size(v_x_1679_);
v___x_1688_ = lean_uint64_of_nat(v_key_1681_);
v___x_1689_ = 32ULL;
v___x_1690_ = lean_uint64_shift_right(v___x_1688_, v___x_1689_);
v_fold_1691_ = lean_uint64_xor(v___x_1688_, v___x_1690_);
v___x_1692_ = 16ULL;
v___x_1693_ = lean_uint64_shift_right(v_fold_1691_, v___x_1692_);
v___x_1694_ = lean_uint64_xor(v_fold_1691_, v___x_1693_);
v___x_1695_ = lean_uint64_to_usize(v___x_1694_);
v___x_1696_ = lean_usize_of_nat(v___x_1687_);
v___x_1697_ = ((size_t)1ULL);
v___x_1698_ = lean_usize_sub(v___x_1696_, v___x_1697_);
v___x_1699_ = lean_usize_land(v___x_1695_, v___x_1698_);
v___x_1700_ = lean_array_uget_borrowed(v_x_1679_, v___x_1699_);
lean_inc(v___x_1700_);
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 2, v___x_1700_);
v___x_1702_ = v___x_1685_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_key_1681_);
lean_ctor_set(v_reuseFailAlloc_1705_, 1, v_value_1682_);
lean_ctor_set(v_reuseFailAlloc_1705_, 2, v___x_1700_);
v___x_1702_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
lean_object* v___x_1703_; 
v___x_1703_ = lean_array_uset(v_x_1679_, v___x_1699_, v___x_1702_);
v_x_1679_ = v___x_1703_;
v_x_1680_ = v_tail_1683_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__3_spec__6___redArg(lean_object* v_i_1707_, lean_object* v_source_1708_, lean_object* v_target_1709_){
_start:
{
lean_object* v___x_1710_; uint8_t v___x_1711_; 
v___x_1710_ = lean_array_get_size(v_source_1708_);
v___x_1711_ = lean_nat_dec_lt(v_i_1707_, v___x_1710_);
if (v___x_1711_ == 0)
{
lean_dec_ref(v_source_1708_);
lean_dec(v_i_1707_);
return v_target_1709_;
}
else
{
lean_object* v_es_1712_; lean_object* v___x_1713_; lean_object* v_source_1714_; lean_object* v_target_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v_es_1712_ = lean_array_fget(v_source_1708_, v_i_1707_);
v___x_1713_ = lean_box(0);
v_source_1714_ = lean_array_fset(v_source_1708_, v_i_1707_, v___x_1713_);
v_target_1715_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__3_spec__6_spec__8___redArg(v_target_1709_, v_es_1712_);
v___x_1716_ = lean_unsigned_to_nat(1u);
v___x_1717_ = lean_nat_add(v_i_1707_, v___x_1716_);
lean_dec(v_i_1707_);
v_i_1707_ = v___x_1717_;
v_source_1708_ = v_source_1714_;
v_target_1709_ = v_target_1715_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__3___redArg(lean_object* v_data_1719_){
_start:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v_nbuckets_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1720_ = lean_array_get_size(v_data_1719_);
v___x_1721_ = lean_unsigned_to_nat(2u);
v_nbuckets_1722_ = lean_nat_mul(v___x_1720_, v___x_1721_);
v___x_1723_ = lean_unsigned_to_nat(0u);
v___x_1724_ = lean_box(0);
v___x_1725_ = lean_mk_array(v_nbuckets_1722_, v___x_1724_);
v___x_1726_ = lean_array_propagate_mark(v_data_1719_, v___x_1725_);
v___x_1727_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__3_spec__6___redArg(v___x_1723_, v_data_1719_, v___x_1726_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1___redArg(lean_object* v_m_1728_, lean_object* v_a_1729_, lean_object* v_b_1730_){
_start:
{
lean_object* v_size_1731_; lean_object* v_buckets_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1775_; 
v_size_1731_ = lean_ctor_get(v_m_1728_, 0);
v_buckets_1732_ = lean_ctor_get(v_m_1728_, 1);
v_isSharedCheck_1775_ = !lean_is_exclusive(v_m_1728_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1734_ = v_m_1728_;
v_isShared_1735_ = v_isSharedCheck_1775_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_buckets_1732_);
lean_inc(v_size_1731_);
lean_dec(v_m_1728_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1775_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; uint64_t v___x_1737_; uint64_t v___x_1738_; uint64_t v___x_1739_; uint64_t v_fold_1740_; uint64_t v___x_1741_; uint64_t v___x_1742_; uint64_t v___x_1743_; size_t v___x_1744_; size_t v___x_1745_; size_t v___x_1746_; size_t v___x_1747_; size_t v___x_1748_; lean_object* v_bkt_1749_; uint8_t v___x_1750_; 
v___x_1736_ = lean_array_get_size(v_buckets_1732_);
v___x_1737_ = lean_uint64_of_nat(v_a_1729_);
v___x_1738_ = 32ULL;
v___x_1739_ = lean_uint64_shift_right(v___x_1737_, v___x_1738_);
v_fold_1740_ = lean_uint64_xor(v___x_1737_, v___x_1739_);
v___x_1741_ = 16ULL;
v___x_1742_ = lean_uint64_shift_right(v_fold_1740_, v___x_1741_);
v___x_1743_ = lean_uint64_xor(v_fold_1740_, v___x_1742_);
v___x_1744_ = lean_uint64_to_usize(v___x_1743_);
v___x_1745_ = lean_usize_of_nat(v___x_1736_);
v___x_1746_ = ((size_t)1ULL);
v___x_1747_ = lean_usize_sub(v___x_1745_, v___x_1746_);
v___x_1748_ = lean_usize_land(v___x_1744_, v___x_1747_);
v_bkt_1749_ = lean_array_uget_borrowed(v_buckets_1732_, v___x_1748_);
v___x_1750_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__2___redArg(v_a_1729_, v_bkt_1749_);
if (v___x_1750_ == 0)
{
lean_object* v___x_1751_; lean_object* v_size_x27_1752_; lean_object* v___x_1753_; lean_object* v_buckets_x27_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; 
v___x_1751_ = lean_unsigned_to_nat(1u);
v_size_x27_1752_ = lean_nat_add(v_size_1731_, v___x_1751_);
lean_dec(v_size_1731_);
lean_inc(v_bkt_1749_);
v___x_1753_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1753_, 0, v_a_1729_);
lean_ctor_set(v___x_1753_, 1, v_b_1730_);
lean_ctor_set(v___x_1753_, 2, v_bkt_1749_);
v_buckets_x27_1754_ = lean_array_uset(v_buckets_1732_, v___x_1748_, v___x_1753_);
v___x_1755_ = lean_unsigned_to_nat(4u);
v___x_1756_ = lean_nat_mul(v_size_x27_1752_, v___x_1755_);
v___x_1757_ = lean_unsigned_to_nat(3u);
v___x_1758_ = lean_nat_div(v___x_1756_, v___x_1757_);
lean_dec(v___x_1756_);
v___x_1759_ = lean_array_get_size(v_buckets_x27_1754_);
v___x_1760_ = lean_nat_dec_le(v___x_1758_, v___x_1759_);
lean_dec(v___x_1758_);
if (v___x_1760_ == 0)
{
lean_object* v_val_1761_; lean_object* v___x_1763_; 
v_val_1761_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__3___redArg(v_buckets_x27_1754_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 1, v_val_1761_);
lean_ctor_set(v___x_1734_, 0, v_size_x27_1752_);
v___x_1763_ = v___x_1734_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_size_x27_1752_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v_val_1761_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
else
{
lean_object* v___x_1766_; 
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 1, v_buckets_x27_1754_);
lean_ctor_set(v___x_1734_, 0, v_size_x27_1752_);
v___x_1766_ = v___x_1734_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_size_x27_1752_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_buckets_x27_1754_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
else
{
lean_object* v___x_1768_; lean_object* v_buckets_x27_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1773_; 
lean_inc(v_bkt_1749_);
v___x_1768_ = lean_box(0);
v_buckets_x27_1769_ = lean_array_uset(v_buckets_1732_, v___x_1748_, v___x_1768_);
v___x_1770_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__4___redArg(v_a_1729_, v_b_1730_, v_bkt_1749_);
v___x_1771_ = lean_array_uset(v_buckets_x27_1769_, v___x_1748_, v___x_1770_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 1, v___x_1771_);
v___x_1773_ = v___x_1734_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_size_1731_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v___x_1771_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__2___redArg(lean_object* v_as_x27_1776_, lean_object* v_b_1777_){
_start:
{
if (lean_obj_tag(v_as_x27_1776_) == 0)
{
return v_b_1777_;
}
else
{
lean_object* v_head_1778_; lean_object* v_tail_1779_; lean_object* v_fst_1780_; lean_object* v_snd_1781_; lean_object* v_r_1782_; 
v_head_1778_ = lean_ctor_get(v_as_x27_1776_, 0);
v_tail_1779_ = lean_ctor_get(v_as_x27_1776_, 1);
v_fst_1780_ = lean_ctor_get(v_head_1778_, 0);
v_snd_1781_ = lean_ctor_get(v_head_1778_, 1);
lean_inc(v_snd_1781_);
lean_inc(v_fst_1780_);
v_r_1782_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1___redArg(v_b_1777_, v_fst_1780_, v_snd_1781_);
v_as_x27_1776_ = v_tail_1779_;
v_b_1777_ = v_r_1782_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__2___redArg___boxed(lean_object* v_as_x27_1784_, lean_object* v_b_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__2___redArg(v_as_x27_1784_, v_b_1785_);
lean_dec(v_as_x27_1784_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1(lean_object* v_m_1787_, lean_object* v_l_1788_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__2___redArg(v_l_1788_, v_m_1787_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1___boxed(lean_object* v_m_1790_, lean_object* v_l_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1(v_m_1790_, v_l_1791_);
lean_dec(v_l_1791_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__2(lean_object* v_x_1793_, lean_object* v_x_1794_){
_start:
{
if (lean_obj_tag(v_x_1794_) == 0)
{
lean_inc(v_x_1793_);
return v_x_1793_;
}
else
{
lean_object* v_key_1795_; lean_object* v_value_1796_; lean_object* v_tail_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v_key_1795_ = lean_ctor_get(v_x_1794_, 0);
v_value_1796_ = lean_ctor_get(v_x_1794_, 1);
v_tail_1797_ = lean_ctor_get(v_x_1794_, 2);
v___x_1798_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__2(v_x_1793_, v_tail_1797_);
lean_inc(v_value_1796_);
lean_inc(v_key_1795_);
v___x_1799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1799_, 0, v_key_1795_);
lean_ctor_set(v___x_1799_, 1, v_value_1796_);
v___x_1800_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
lean_ctor_set(v___x_1800_, 1, v___x_1798_);
return v___x_1800_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__2___boxed(lean_object* v_x_1801_, lean_object* v_x_1802_){
_start:
{
lean_object* v_res_1803_; 
v_res_1803_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__2(v_x_1801_, v_x_1802_);
lean_dec(v_x_1802_);
lean_dec(v_x_1801_);
return v_res_1803_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__3(lean_object* v_as_1804_, size_t v_i_1805_, size_t v_stop_1806_, lean_object* v_b_1807_){
_start:
{
uint8_t v___x_1808_; 
v___x_1808_ = lean_usize_dec_eq(v_i_1805_, v_stop_1806_);
if (v___x_1808_ == 0)
{
size_t v___x_1809_; size_t v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1809_ = ((size_t)1ULL);
v___x_1810_ = lean_usize_sub(v_i_1805_, v___x_1809_);
v___x_1811_ = lean_array_uget_borrowed(v_as_1804_, v___x_1810_);
v___x_1812_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__2(v_b_1807_, v___x_1811_);
lean_dec(v_b_1807_);
v_i_1805_ = v___x_1810_;
v_b_1807_ = v___x_1812_;
goto _start;
}
else
{
return v_b_1807_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1804_ = stack[0].m_obj;
size_t v_i_1805_ = stack[1].m_num;
size_t v_stop_1806_ = stack[2].m_num;
lean_object* v_b_1807_ = stack[3].m_obj;
lean_object* v_res_1814_;
v_res_1814_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__3(v_as_1804_, v_i_1805_, v_stop_1806_, v_b_1807_);
stack->m_obj
 = v_res_1814_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__3___boxed(lean_object* v_as_1815_, lean_object* v_i_1816_, lean_object* v_stop_1817_, lean_object* v_b_1818_){
_start:
{
size_t v_i_boxed_1819_; size_t v_stop_boxed_1820_; lean_object* v_res_1821_; 
v_i_boxed_1819_ = lean_unbox_usize(v_i_1816_);
lean_dec(v_i_1816_);
v_stop_boxed_1820_ = lean_unbox_usize(v_stop_1817_);
lean_dec(v_stop_1817_);
v_res_1821_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__3(v_as_1815_, v_i_boxed_1819_, v_stop_boxed_1820_, v_b_1818_);
lean_dec_ref(v_as_1815_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__0(lean_object* v_a_1822_, lean_object* v_a_1823_){
_start:
{
if (lean_obj_tag(v_a_1822_) == 0)
{
lean_object* v___x_1824_; 
v___x_1824_ = l_List_reverse___redArg(v_a_1823_);
return v___x_1824_;
}
else
{
lean_object* v_head_1825_; lean_object* v_snd_1826_; lean_object* v_tail_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1850_; 
v_head_1825_ = lean_ctor_get(v_a_1822_, 0);
lean_inc(v_head_1825_);
v_snd_1826_ = lean_ctor_get(v_head_1825_, 1);
lean_inc(v_snd_1826_);
v_tail_1827_ = lean_ctor_get(v_a_1822_, 1);
v_isSharedCheck_1850_ = !lean_is_exclusive(v_a_1822_);
if (v_isSharedCheck_1850_ == 0)
{
lean_object* v_unused_1851_; 
v_unused_1851_ = lean_ctor_get(v_a_1822_, 0);
lean_dec(v_unused_1851_);
v___x_1829_ = v_a_1822_;
v_isShared_1830_ = v_isSharedCheck_1850_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_tail_1827_);
lean_dec(v_a_1822_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1850_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v_fst_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1848_; 
v_fst_1831_ = lean_ctor_get(v_head_1825_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v_head_1825_);
if (v_isSharedCheck_1848_ == 0)
{
lean_object* v_unused_1849_; 
v_unused_1849_ = lean_ctor_get(v_head_1825_, 1);
lean_dec(v_unused_1849_);
v___x_1833_ = v_head_1825_;
v_isShared_1834_ = v_isSharedCheck_1848_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_fst_1831_);
lean_dec(v_head_1825_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1848_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v_width_1835_; lean_object* v_atomNumber_1836_; uint8_t v_synthetic_1837_; lean_object* v___x_1838_; lean_object* v___x_1840_; 
v_width_1835_ = lean_ctor_get(v_snd_1826_, 0);
lean_inc(v_width_1835_);
v_atomNumber_1836_ = lean_ctor_get(v_snd_1826_, 1);
lean_inc(v_atomNumber_1836_);
v_synthetic_1837_ = lean_ctor_get_uint8(v_snd_1826_, sizeof(void*)*2);
lean_dec(v_snd_1826_);
v___x_1838_ = lean_box(v_synthetic_1837_);
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 1, v___x_1838_);
v___x_1840_ = v___x_1833_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_fst_1831_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v___x_1838_);
v___x_1840_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1841_, 0, v_width_1835_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
v___x_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1842_, 0, v_atomNumber_1836_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 1, v_a_1823_);
lean_ctor_set(v___x_1829_, 0, v___x_1842_);
v___x_1844_ = v___x_1829_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1842_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v_a_1823_);
v___x_1844_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
v_a_1822_ = v_tail_1827_;
v_a_1823_ = v___x_1844_;
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
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1852_ = lean_box(0);
v___x_1853_ = lean_unsigned_to_nat(16u);
v___x_1854_ = lean_mk_array(v___x_1853_, v___x_1852_);
return v___x_1854_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg___closed__1(void){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1855_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg___closed__0, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg___closed__0_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg___closed__0);
v___x_1856_ = lean_unsigned_to_nat(0u);
v___x_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
lean_ctor_set(v___x_1857_, 1, v___x_1855_);
return v___x_1857_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg(lean_object* v_a_1858_){
_start:
{
lean_object* v___x_1860_; lean_object* v___y_1862_; lean_object* v_atoms_1883_; lean_object* v_buckets_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; uint8_t v___x_1888_; 
v___x_1860_ = lean_st_ref_get(v_a_1858_);
v_atoms_1883_ = lean_ctor_get(v___x_1860_, 0);
lean_inc_ref(v_atoms_1883_);
lean_dec(v___x_1860_);
v_buckets_1884_ = lean_ctor_get(v_atoms_1883_, 1);
lean_inc_ref(v_buckets_1884_);
lean_dec_ref(v_atoms_1883_);
v___x_1885_ = lean_box(0);
v___x_1886_ = lean_array_get_size(v_buckets_1884_);
v___x_1887_ = lean_unsigned_to_nat(0u);
v___x_1888_ = lean_nat_dec_lt(v___x_1887_, v___x_1886_);
if (v___x_1888_ == 0)
{
lean_dec_ref(v_buckets_1884_);
v___y_1862_ = v___x_1885_;
goto v___jp_1861_;
}
else
{
size_t v___x_1889_; size_t v___x_1890_; lean_object* v___x_1891_; 
v___x_1889_ = lean_usize_of_nat(v___x_1886_);
v___x_1890_ = ((size_t)0ULL);
v___x_1891_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__3(v_buckets_1884_, v___x_1889_, v___x_1890_, v___x_1885_);
lean_dec_ref(v_buckets_1884_);
v___y_1862_ = v___x_1891_;
goto v___jp_1861_;
}
v___jp_1861_:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v_atoms_1868_; lean_object* v_atomsAssignmentExprCache_1869_; lean_object* v_evalsAtCache_1870_; lean_object* v_theoryState_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1881_; 
v___x_1863_ = lean_box(0);
v___x_1864_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__0(v___y_1862_, v___x_1863_);
v___x_1865_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg___closed__1);
v___x_1866_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__2___redArg(v___x_1864_, v___x_1865_);
lean_dec(v___x_1864_);
v___x_1867_ = lean_st_ref_take(v_a_1858_);
v_atoms_1868_ = lean_ctor_get(v___x_1867_, 0);
v_atomsAssignmentExprCache_1869_ = lean_ctor_get(v___x_1867_, 1);
v_evalsAtCache_1870_ = lean_ctor_get(v___x_1867_, 3);
v_theoryState_1871_ = lean_ctor_get(v___x_1867_, 4);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1881_ == 0)
{
lean_object* v_unused_1882_; 
v_unused_1882_ = lean_ctor_get(v___x_1867_, 2);
lean_dec(v_unused_1882_);
v___x_1873_ = v___x_1867_;
v_isShared_1874_ = v_isSharedCheck_1881_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_theoryState_1871_);
lean_inc(v_evalsAtCache_1870_);
lean_inc(v_atomsAssignmentExprCache_1869_);
lean_inc(v_atoms_1868_);
lean_dec(v___x_1867_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1881_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; lean_object* v___x_1877_; 
lean_inc_ref(v___x_1866_);
v___x_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1866_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 2, v___x_1875_);
v___x_1877_ = v___x_1873_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_atoms_1868_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v_atomsAssignmentExprCache_1869_);
lean_ctor_set(v_reuseFailAlloc_1880_, 2, v___x_1875_);
lean_ctor_set(v_reuseFailAlloc_1880_, 3, v_evalsAtCache_1870_);
lean_ctor_set(v_reuseFailAlloc_1880_, 4, v_theoryState_1871_);
v___x_1877_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = lean_st_ref_put(v_a_1858_, v___x_1877_);
v___x_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1866_);
return v___x_1879_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1858_ = stack[0].m_obj;
lean_object* v_res_1892_;
v_res_1892_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg(v_a_1858_);
stack->m_obj
 = v_res_1892_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg___boxed(lean_object* v_a_1893_, lean_object* v_a_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg(v_a_1893_);
lean_dec(v_a_1893_);
return v_res_1895_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment(lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_){
_start:
{
lean_object* v___x_1908_; 
v___x_1908_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg(v_a_1897_);
return v___x_1908_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1896_ = stack[0].m_obj;
lean_object* v_a_1897_ = stack[1].m_obj;
lean_object* v_a_1898_ = stack[2].m_obj;
lean_object* v_a_1899_ = stack[3].m_obj;
lean_object* v_a_1900_ = stack[4].m_obj;
lean_object* v_a_1901_ = stack[5].m_obj;
lean_object* v_a_1902_ = stack[6].m_obj;
lean_object* v_a_1903_ = stack[7].m_obj;
lean_object* v_a_1904_ = stack[8].m_obj;
lean_object* v_a_1905_ = stack[9].m_obj;
lean_object* v_a_1906_ = stack[10].m_obj;
lean_object* v_res_1909_;
v_res_1909_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment(v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
stack->m_obj
 = v_res_1909_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___boxed(lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_, lean_object* v_a_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment(v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_, v_a_1919_, v_a_1920_);
lean_dec(v_a_1920_);
lean_dec_ref(v_a_1919_);
lean_dec(v_a_1918_);
lean_dec_ref(v_a_1917_);
lean_dec(v_a_1916_);
lean_dec_ref(v_a_1915_);
lean_dec(v_a_1914_);
lean_dec_ref(v_a_1913_);
lean_dec(v_a_1912_);
lean_dec(v_a_1911_);
lean_dec_ref(v_a_1910_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1(lean_object* v_00_u03b2_1923_, lean_object* v_m_1924_, lean_object* v_a_1925_, lean_object* v_b_1926_){
_start:
{
lean_object* v___x_1927_; 
v___x_1927_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1___redArg(v_m_1924_, v_a_1925_, v_b_1926_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__2(lean_object* v_as_1928_, lean_object* v_as_x27_1929_, lean_object* v_b_1930_, lean_object* v_a_1931_){
_start:
{
lean_object* v___x_1932_; 
v___x_1932_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__2___redArg(v_as_x27_1929_, v_b_1930_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__2___boxed(lean_object* v_as_1933_, lean_object* v_as_x27_1934_, lean_object* v_b_1935_, lean_object* v_a_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__2(v_as_1933_, v_as_x27_1934_, v_b_1935_, v_a_1936_);
lean_dec(v_as_x27_1934_);
lean_dec(v_as_1933_);
return v_res_1937_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1938_, lean_object* v_a_1939_, lean_object* v_x_1940_){
_start:
{
uint8_t v___x_1941_; 
v___x_1941_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__2___redArg(v_a_1939_, v_x_1940_);
return v___x_1941_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1939_ = stack[1].m_obj;
lean_object* v_x_1940_ = stack[2].m_obj;
uint8_t v_res_1942_;
v_res_1942_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__2(lean_box(0), v_a_1939_, v_x_1940_);
stack->m_num = v_res_1942_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1943_, lean_object* v_a_1944_, lean_object* v_x_1945_){
_start:
{
uint8_t v_res_1946_; lean_object* v_r_1947_; 
v_res_1946_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__2(v_00_u03b2_1943_, v_a_1944_, v_x_1945_);
lean_dec(v_x_1945_);
lean_dec(v_a_1944_);
v_r_1947_ = lean_box(v_res_1946_);
return v_r_1947_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_1948_, lean_object* v_data_1949_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__3___redArg(v_data_1949_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__4(lean_object* v_00_u03b2_1951_, lean_object* v_a_1952_, lean_object* v_b_1953_, lean_object* v_x_1954_){
_start:
{
lean_object* v___x_1955_; 
v___x_1955_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__4___redArg(v_a_1952_, v_b_1953_, v_x_1954_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_1956_, lean_object* v_i_1957_, lean_object* v_source_1958_, lean_object* v_target_1959_){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__3_spec__6___redArg(v_i_1957_, v_source_1958_, v_target_1959_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__3_spec__6_spec__8(lean_object* v_00_u03b2_1961_, lean_object* v_x_1962_, lean_object* v_x_1963_){
_start:
{
lean_object* v___x_1964_; 
v___x_1964_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment_spec__1_spec__1_spec__3_spec__6_spec__8___redArg(v_x_1962_, v_x_1963_);
return v___x_1964_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(lean_object* v_a_1965_){
_start:
{
lean_object* v___x_1967_; lean_object* v_atomsAssignmentMapCache_1968_; 
v___x_1967_ = lean_st_ref_get(v_a_1965_);
v_atomsAssignmentMapCache_1968_ = lean_ctor_get(v___x_1967_, 2);
lean_inc(v_atomsAssignmentMapCache_1968_);
lean_dec(v___x_1967_);
if (lean_obj_tag(v_atomsAssignmentMapCache_1968_) == 0)
{
lean_object* v___x_1969_; 
v___x_1969_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_updateAtomsAssignment___redArg(v_a_1965_);
return v___x_1969_;
}
else
{
lean_object* v_val_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
v_val_1970_ = lean_ctor_get(v_atomsAssignmentMapCache_1968_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v_atomsAssignmentMapCache_1968_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v_atomsAssignmentMapCache_1968_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_val_1970_);
lean_dec(v_atomsAssignmentMapCache_1968_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
lean_ctor_set_tag(v___x_1972_, 0);
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_val_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1965_ = stack[0].m_obj;
lean_object* v_res_1978_;
v_res_1978_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(v_a_1965_);
stack->m_obj
 = v_res_1978_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg___boxed(lean_object* v_a_1979_, lean_object* v_a_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(v_a_1979_);
lean_dec(v_a_1979_);
return v_res_1981_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap(lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___redArg(v_a_1983_);
return v___x_1994_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1982_ = stack[0].m_obj;
lean_object* v_a_1983_ = stack[1].m_obj;
lean_object* v_a_1984_ = stack[2].m_obj;
lean_object* v_a_1985_ = stack[3].m_obj;
lean_object* v_a_1986_ = stack[4].m_obj;
lean_object* v_a_1987_ = stack[5].m_obj;
lean_object* v_a_1988_ = stack[6].m_obj;
lean_object* v_a_1989_ = stack[7].m_obj;
lean_object* v_a_1990_ = stack[8].m_obj;
lean_object* v_a_1991_ = stack[9].m_obj;
lean_object* v_a_1992_ = stack[10].m_obj;
lean_object* v_res_1995_;
v_res_1995_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap(v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_);
stack->m_obj
 = v_res_1995_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap___boxed(lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentMap(v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_);
lean_dec(v_a_2006_);
lean_dec_ref(v_a_2005_);
lean_dec(v_a_2004_);
lean_dec_ref(v_a_2003_);
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec(v_a_1997_);
lean_dec_ref(v_a_1996_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___lam__0(lean_object* v___x_2010_, lean_object* v___x_2011_, lean_object* v___x_2012_, lean_object* v___x_2013_, lean_object* v___x_2014_, lean_object* v___x_2015_, lean_object* v_x_2016_){
_start:
{
lean_object* v_fst_2017_; lean_object* v_snd_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v_fst_2017_ = lean_ctor_get(v_x_2016_, 0);
lean_inc(v_fst_2017_);
v_snd_2018_ = lean_ctor_get(v_x_2016_, 1);
lean_inc(v_snd_2018_);
lean_dec_ref(v_x_2016_);
v___x_2019_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___lam__0___closed__0));
v___x_2020_ = l_Lean_Name_mkStr6(v___x_2010_, v___x_2011_, v___x_2012_, v___x_2013_, v___x_2014_, v___x_2019_);
v___x_2021_ = l_Lean_mkConst(v___x_2020_, v___x_2015_);
v___x_2022_ = l_Lean_mkNatLit(v_fst_2017_);
v___x_2023_ = l_Lean_mkAppB(v___x_2021_, v___x_2022_, v_snd_2018_);
return v___x_2023_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0_spec__0(lean_object* v_msgData_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v___x_2030_; lean_object* v_env_2031_; uint8_t v___x_2032_; lean_object* v_env_2033_; lean_object* v___x_2034_; lean_object* v_toCold_2035_; lean_object* v_mctx_2036_; lean_object* v_lctx_2037_; lean_object* v_options_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2030_ = lean_st_ref_get(v___y_2028_);
v_env_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc_ref(v_env_2031_);
lean_dec(v___x_2030_);
v___x_2032_ = 0;
v_env_2033_ = l_Lean_Environment_setRecordingDeps(v_env_2031_, v___x_2032_);
v___x_2034_ = lean_st_ref_get(v___y_2026_);
v_toCold_2035_ = lean_ctor_get(v___y_2027_, 0);
v_mctx_2036_ = lean_ctor_get(v___x_2034_, 0);
lean_inc_ref(v_mctx_2036_);
lean_dec(v___x_2034_);
v_lctx_2037_ = lean_ctor_get(v___y_2025_, 2);
v_options_2038_ = lean_ctor_get(v_toCold_2035_, 2);
lean_inc_ref(v_options_2038_);
lean_inc_ref(v_lctx_2037_);
v___x_2039_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2039_, 0, v_env_2033_);
lean_ctor_set(v___x_2039_, 1, v_mctx_2036_);
lean_ctor_set(v___x_2039_, 2, v_lctx_2037_);
lean_ctor_set(v___x_2039_, 3, v_options_2038_);
v___x_2040_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2039_);
lean_ctor_set(v___x_2040_, 1, v_msgData_2024_);
v___x_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2040_);
return v___x_2041_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_2024_ = stack[0].m_obj;
lean_object* v___y_2025_ = stack[1].m_obj;
lean_object* v___y_2026_ = stack[2].m_obj;
lean_object* v___y_2027_ = stack[3].m_obj;
lean_object* v___y_2028_ = stack[4].m_obj;
lean_object* v_res_2042_;
v_res_2042_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0_spec__0(v_msgData_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
stack->m_obj
 = v_res_2042_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0_spec__0___boxed(lean_object* v_msgData_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0_spec__0(v_msgData_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
return v_res_2049_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0___redArg(lean_object* v_msg_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v_ref_2056_; lean_object* v___x_2057_; lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2066_; 
v_ref_2056_ = lean_ctor_get(v___y_2053_, 2);
v___x_2057_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0_spec__0(v_msg_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2060_ = v___x_2057_;
v_isShared_2061_ = v_isSharedCheck_2066_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2057_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2066_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2062_; lean_object* v___x_2064_; 
lean_inc(v_ref_2056_);
v___x_2062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2062_, 0, v_ref_2056_);
lean_ctor_set(v___x_2062_, 1, v_a_2058_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set_tag(v___x_2060_, 1);
lean_ctor_set(v___x_2060_, 0, v___x_2062_);
v___x_2064_ = v___x_2060_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v___x_2062_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2050_ = stack[0].m_obj;
lean_object* v___y_2051_ = stack[1].m_obj;
lean_object* v___y_2052_ = stack[2].m_obj;
lean_object* v___y_2053_ = stack[3].m_obj;
lean_object* v___y_2054_ = stack[4].m_obj;
lean_object* v_res_2067_;
v_res_2067_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0___redArg(v_msg_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
stack->m_obj
 = v_res_2067_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0___redArg___boxed(lean_object* v_msg_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0___redArg(v_msg_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
return v_res_2074_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__1(void){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2076_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__0));
v___x_2077_ = l_Lean_stringToMessageData(v___x_2076_);
return v___x_2077_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__5(void){
_start:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2092_ = lean_box(0);
v___x_2093_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__3));
v___x_2094_ = l_Lean_mkConst(v___x_2093_, v___x_2092_);
return v___x_2094_;
}
}
lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment(lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_){
_start:
{
lean_object* v___x_2107_; lean_object* v_a_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; 
v___x_2107_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atoms___redArg(v_a_2096_);
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_a_2108_);
lean_dec_ref(v___x_2107_);
v___x_2109_ = lean_unsigned_to_nat(0u);
v___x_2110_ = lean_array_get_size(v_a_2108_);
v___x_2111_ = lean_nat_dec_lt(v___x_2109_, v___x_2110_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
lean_dec(v_a_2108_);
v___x_2112_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__1, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__1_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__1);
v___x_2113_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0___redArg(v___x_2112_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
return v___x_2113_;
}
else
{
lean_object* v___x_2114_; lean_object* v___f_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2114_ = l_Lean_RArray_ofArray___redArg(v_a_2108_);
v___f_2115_ = ((lean_object*)(l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__4));
v___x_2116_ = lean_obj_once(&l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__5, &l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__5_once, _init_l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___closed__5);
v___x_2117_ = l_Lean_RArray_toExpr___redArg(v___x_2116_, v___f_2115_, v___x_2114_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2148_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2120_ = v___x_2117_;
v_isShared_2121_ = v_isSharedCheck_2148_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2117_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2148_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Lean_Meta_Sym_shareCommon(v_a_2118_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2147_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2125_ = v___x_2122_;
v_isShared_2126_ = v_isSharedCheck_2147_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2122_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2147_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2127_; lean_object* v_atoms_2128_; lean_object* v_atomsAssignmentMapCache_2129_; lean_object* v_evalsAtCache_2130_; lean_object* v_theoryState_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2145_; 
v___x_2127_ = lean_st_ref_take(v_a_2096_);
v_atoms_2128_ = lean_ctor_get(v___x_2127_, 0);
v_atomsAssignmentMapCache_2129_ = lean_ctor_get(v___x_2127_, 2);
v_evalsAtCache_2130_ = lean_ctor_get(v___x_2127_, 3);
v_theoryState_2131_ = lean_ctor_get(v___x_2127_, 4);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2127_);
if (v_isSharedCheck_2145_ == 0)
{
lean_object* v_unused_2146_; 
v_unused_2146_ = lean_ctor_get(v___x_2127_, 1);
lean_dec(v_unused_2146_);
v___x_2133_ = v___x_2127_;
v_isShared_2134_ = v_isSharedCheck_2145_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_theoryState_2131_);
lean_inc(v_evalsAtCache_2130_);
lean_inc(v_atomsAssignmentMapCache_2129_);
lean_inc(v_atoms_2128_);
lean_dec(v___x_2127_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2145_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
lean_inc(v_a_2123_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set_tag(v___x_2120_, 1);
lean_ctor_set(v___x_2120_, 0, v_a_2123_);
v___x_2136_ = v___x_2120_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2123_);
v___x_2136_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
lean_object* v___x_2138_; 
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 1, v___x_2136_);
v___x_2138_ = v___x_2133_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_atoms_2128_);
lean_ctor_set(v_reuseFailAlloc_2143_, 1, v___x_2136_);
lean_ctor_set(v_reuseFailAlloc_2143_, 2, v_atomsAssignmentMapCache_2129_);
lean_ctor_set(v_reuseFailAlloc_2143_, 3, v_evalsAtCache_2130_);
lean_ctor_set(v_reuseFailAlloc_2143_, 4, v_theoryState_2131_);
v___x_2138_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
lean_object* v___x_2139_; lean_object* v___x_2141_; 
v___x_2139_ = lean_st_ref_put(v_a_2096_, v___x_2138_);
if (v_isShared_2126_ == 0)
{
v___x_2141_ = v___x_2125_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2123_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_2120_);
return v___x_2122_;
}
}
}
else
{
return v___x_2117_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2095_ = stack[0].m_obj;
lean_object* v_a_2096_ = stack[1].m_obj;
lean_object* v_a_2097_ = stack[2].m_obj;
lean_object* v_a_2098_ = stack[3].m_obj;
lean_object* v_a_2099_ = stack[4].m_obj;
lean_object* v_a_2100_ = stack[5].m_obj;
lean_object* v_a_2101_ = stack[6].m_obj;
lean_object* v_a_2102_ = stack[7].m_obj;
lean_object* v_a_2103_ = stack[8].m_obj;
lean_object* v_a_2104_ = stack[9].m_obj;
lean_object* v_a_2105_ = stack[10].m_obj;
lean_object* v_res_2149_;
v_res_2149_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment(v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
stack->m_obj
 = v_res_2149_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment___boxed(lean_object* v_a_2150_, lean_object* v_a_2151_, lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment(v_a_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_);
lean_dec(v_a_2160_);
lean_dec_ref(v_a_2159_);
lean_dec(v_a_2158_);
lean_dec_ref(v_a_2157_);
lean_dec(v_a_2156_);
lean_dec_ref(v_a_2155_);
lean_dec(v_a_2154_);
lean_dec_ref(v_a_2153_);
lean_dec(v_a_2152_);
lean_dec(v_a_2151_);
lean_dec_ref(v_a_2150_);
return v_res_2162_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0(lean_object* v_00_u03b1_2163_, lean_object* v_msg_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v___x_2177_; 
v___x_2177_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0___redArg(v_msg_2164_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
return v___x_2177_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2164_ = stack[1].m_obj;
lean_object* v___y_2165_ = stack[2].m_obj;
lean_object* v___y_2166_ = stack[3].m_obj;
lean_object* v___y_2167_ = stack[4].m_obj;
lean_object* v___y_2168_ = stack[5].m_obj;
lean_object* v___y_2169_ = stack[6].m_obj;
lean_object* v___y_2170_ = stack[7].m_obj;
lean_object* v___y_2171_ = stack[8].m_obj;
lean_object* v___y_2172_ = stack[9].m_obj;
lean_object* v___y_2173_ = stack[10].m_obj;
lean_object* v___y_2174_ = stack[11].m_obj;
lean_object* v___y_2175_ = stack[12].m_obj;
lean_object* v_res_2178_;
v_res_2178_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0(lean_box(0), v_msg_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
stack->m_obj
 = v_res_2178_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0___boxed(lean_object* v_00_u03b1_2179_, lean_object* v_msg_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0(v_00_u03b1_2179_, v_msg_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
return v_res_2193_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr(lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_){
_start:
{
lean_object* v___x_2206_; lean_object* v_atomsAssignmentExprCache_2207_; 
v___x_2206_ = lean_st_ref_get(v_a_2195_);
v_atomsAssignmentExprCache_2207_ = lean_ctor_get(v___x_2206_, 1);
lean_inc(v_atomsAssignmentExprCache_2207_);
lean_dec(v___x_2206_);
if (lean_obj_tag(v_atomsAssignmentExprCache_2207_) == 0)
{
lean_object* v___x_2208_; 
v___x_2208_ = l___private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment(v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_);
return v___x_2208_;
}
else
{
lean_object* v_val_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
v_val_2209_ = lean_ctor_get(v_atomsAssignmentExprCache_2207_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v_atomsAssignmentExprCache_2207_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v_atomsAssignmentExprCache_2207_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_val_2209_);
lean_dec(v_atomsAssignmentExprCache_2207_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
lean_ctor_set_tag(v___x_2211_, 0);
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_val_2209_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
return v___x_2214_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2194_ = stack[0].m_obj;
lean_object* v_a_2195_ = stack[1].m_obj;
lean_object* v_a_2196_ = stack[2].m_obj;
lean_object* v_a_2197_ = stack[3].m_obj;
lean_object* v_a_2198_ = stack[4].m_obj;
lean_object* v_a_2199_ = stack[5].m_obj;
lean_object* v_a_2200_ = stack[6].m_obj;
lean_object* v_a_2201_ = stack[7].m_obj;
lean_object* v_a_2202_ = stack[8].m_obj;
lean_object* v_a_2203_ = stack[9].m_obj;
lean_object* v_a_2204_ = stack[10].m_obj;
lean_object* v_res_2217_;
v_res_2217_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr(v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_, v_a_2199_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_);
stack->m_obj
 = v_res_2217_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr___boxed(lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr(v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_);
lean_dec(v_a_2228_);
lean_dec_ref(v_a_2227_);
lean_dec(v_a_2226_);
lean_dec_ref(v_a_2225_);
lean_dec(v_a_2224_);
lean_dec_ref(v_a_2223_);
lean_dec(v_a_2222_);
lean_dec_ref(v_a_2221_);
lean_dec(v_a_2220_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
return v_res_2230_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_ReifyM_isAtom_spec__0___redArg(lean_object* v_m_2231_, lean_object* v_a_2232_){
_start:
{
lean_object* v_buckets_2233_; lean_object* v___x_2234_; size_t v___x_2235_; size_t v___x_2236_; size_t v___x_2237_; uint64_t v___x_2238_; uint64_t v___x_2239_; uint64_t v___x_2240_; uint64_t v_fold_2241_; uint64_t v___x_2242_; uint64_t v___x_2243_; uint64_t v___x_2244_; size_t v___x_2245_; size_t v___x_2246_; size_t v___x_2247_; size_t v___x_2248_; size_t v___x_2249_; lean_object* v___x_2250_; uint8_t v___x_2251_; 
v_buckets_2233_ = lean_ctor_get(v_m_2231_, 1);
v___x_2234_ = lean_array_get_size(v_buckets_2233_);
v___x_2235_ = lean_ptr_addr(v_a_2232_);
v___x_2236_ = ((size_t)3ULL);
v___x_2237_ = lean_usize_shift_right(v___x_2235_, v___x_2236_);
v___x_2238_ = lean_usize_to_uint64(v___x_2237_);
v___x_2239_ = 32ULL;
v___x_2240_ = lean_uint64_shift_right(v___x_2238_, v___x_2239_);
v_fold_2241_ = lean_uint64_xor(v___x_2238_, v___x_2240_);
v___x_2242_ = 16ULL;
v___x_2243_ = lean_uint64_shift_right(v_fold_2241_, v___x_2242_);
v___x_2244_ = lean_uint64_xor(v_fold_2241_, v___x_2243_);
v___x_2245_ = lean_uint64_to_usize(v___x_2244_);
v___x_2246_ = lean_usize_of_nat(v___x_2234_);
v___x_2247_ = ((size_t)1ULL);
v___x_2248_ = lean_usize_sub(v___x_2246_, v___x_2247_);
v___x_2249_ = lean_usize_land(v___x_2245_, v___x_2248_);
v___x_2250_ = lean_array_uget_borrowed(v_buckets_2233_, v___x_2249_);
v___x_2251_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1_spec__2___redArg(v_a_2232_, v___x_2250_);
return v___x_2251_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_ReifyM_isAtom_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_2231_ = stack[0].m_obj;
lean_object* v_a_2232_ = stack[1].m_obj;
uint8_t v_res_2252_;
v_res_2252_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_ReifyM_isAtom_spec__0___redArg(v_m_2231_, v_a_2232_);
stack->m_num = v_res_2252_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_ReifyM_isAtom_spec__0___redArg___boxed(lean_object* v_m_2253_, lean_object* v_a_2254_){
_start:
{
uint8_t v_res_2255_; lean_object* v_r_2256_; 
v_res_2255_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_ReifyM_isAtom_spec__0___redArg(v_m_2253_, v_a_2254_);
lean_dec_ref(v_a_2254_);
lean_dec_ref(v_m_2253_);
v_r_2256_ = lean_box(v_res_2255_);
return v_r_2256_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_isAtom___redArg(lean_object* v_e_2257_, lean_object* v_a_2258_){
_start:
{
lean_object* v___x_2260_; lean_object* v_atoms_2261_; uint8_t v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2260_ = lean_st_ref_get(v_a_2258_);
v_atoms_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc_ref(v_atoms_2261_);
lean_dec(v___x_2260_);
v___x_2262_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_ReifyM_isAtom_spec__0___redArg(v_atoms_2261_, v_e_2257_);
lean_dec_ref(v_atoms_2261_);
v___x_2263_ = lean_box(v___x_2262_);
v___x_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2263_);
return v___x_2264_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_ReifyM_isAtom___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2257_ = stack[0].m_obj;
lean_object* v_a_2258_ = stack[1].m_obj;
lean_object* v_res_2265_;
v_res_2265_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_isAtom___redArg(v_e_2257_, v_a_2258_);
stack->m_obj
 = v_res_2265_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_isAtom___redArg___boxed(lean_object* v_e_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_isAtom___redArg(v_e_2266_, v_a_2267_);
lean_dec(v_a_2267_);
lean_dec_ref(v_e_2266_);
return v_res_2269_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_isAtom(lean_object* v_e_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_isAtom___redArg(v_e_2270_, v_a_2272_);
return v___x_2283_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_ReifyM_isAtom_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2270_ = stack[0].m_obj;
lean_object* v_a_2271_ = stack[1].m_obj;
lean_object* v_a_2272_ = stack[2].m_obj;
lean_object* v_a_2273_ = stack[3].m_obj;
lean_object* v_a_2274_ = stack[4].m_obj;
lean_object* v_a_2275_ = stack[5].m_obj;
lean_object* v_a_2276_ = stack[6].m_obj;
lean_object* v_a_2277_ = stack[7].m_obj;
lean_object* v_a_2278_ = stack[8].m_obj;
lean_object* v_a_2279_ = stack[9].m_obj;
lean_object* v_a_2280_ = stack[10].m_obj;
lean_object* v_a_2281_ = stack[11].m_obj;
lean_object* v_res_2284_;
v_res_2284_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_isAtom(v_e_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_);
stack->m_obj
 = v_res_2284_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_isAtom___boxed(lean_object* v_e_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_isAtom(v_e_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
lean_dec(v_a_2296_);
lean_dec_ref(v_a_2295_);
lean_dec(v_a_2294_);
lean_dec_ref(v_a_2293_);
lean_dec(v_a_2292_);
lean_dec_ref(v_a_2291_);
lean_dec(v_a_2290_);
lean_dec_ref(v_a_2289_);
lean_dec(v_a_2288_);
lean_dec(v_a_2287_);
lean_dec_ref(v_a_2286_);
lean_dec_ref(v_e_2285_);
return v_res_2298_;
}
}
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_ReifyM_isAtom_spec__0(lean_object* v_00_u03b2_2299_, lean_object* v_m_2300_, lean_object* v_a_2301_){
_start:
{
uint8_t v___x_2302_; 
v___x_2302_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_ReifyM_isAtom_spec__0___redArg(v_m_2300_, v_a_2301_);
return v___x_2302_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_ReifyM_isAtom_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_2300_ = stack[1].m_obj;
lean_object* v_a_2301_ = stack[2].m_obj;
uint8_t v_res_2303_;
v_res_2303_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_ReifyM_isAtom_spec__0(lean_box(0), v_m_2300_, v_a_2301_);
stack->m_num = v_res_2303_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_ReifyM_isAtom_spec__0___boxed(lean_object* v_00_u03b2_2304_, lean_object* v_m_2305_, lean_object* v_a_2306_){
_start:
{
uint8_t v_res_2307_; lean_object* v_r_2308_; 
v_res_2307_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_BVDecide_ReifyM_isAtom_spec__0(v_00_u03b2_2304_, v_m_2305_, v_a_2306_);
lean_dec_ref(v_a_2306_);
lean_dec_ref(v_m_2305_);
v_r_2308_ = lean_box(v_res_2307_);
return v_r_2308_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_getAtomNumber___redArg(lean_object* v_e_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v___x_2312_; lean_object* v_atoms_2313_; lean_object* v___x_2314_; 
v___x_2312_ = lean_st_ref_get(v_a_2310_);
v_atoms_2313_ = lean_ctor_get(v___x_2312_, 0);
lean_inc_ref(v_atoms_2313_);
lean_dec(v___x_2312_);
v___x_2314_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_atoms_2313_, v_e_2309_);
lean_dec_ref(v_atoms_2313_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = lean_box(0);
v___x_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
return v___x_2316_;
}
else
{
lean_object* v_val_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2326_; 
v_val_2317_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2319_ = v___x_2314_;
v_isShared_2320_ = v_isSharedCheck_2326_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_val_2317_);
lean_dec(v___x_2314_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2326_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v_atomNumber_2321_; lean_object* v___x_2323_; 
v_atomNumber_2321_ = lean_ctor_get(v_val_2317_, 1);
lean_inc(v_atomNumber_2321_);
lean_dec(v_val_2317_);
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 0, v_atomNumber_2321_);
v___x_2323_ = v___x_2319_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_atomNumber_2321_);
v___x_2323_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
lean_object* v___x_2324_; 
v___x_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2323_);
return v___x_2324_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_ReifyM_getAtomNumber___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2309_ = stack[0].m_obj;
lean_object* v_a_2310_ = stack[1].m_obj;
lean_object* v_res_2327_;
v_res_2327_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_getAtomNumber___redArg(v_e_2309_, v_a_2310_);
stack->m_obj
 = v_res_2327_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_getAtomNumber___redArg___boxed(lean_object* v_e_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_getAtomNumber___redArg(v_e_2328_, v_a_2329_);
lean_dec(v_a_2329_);
lean_dec_ref(v_e_2328_);
return v_res_2331_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_getAtomNumber(lean_object* v_e_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_getAtomNumber___redArg(v_e_2332_, v_a_2334_);
return v___x_2345_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_ReifyM_getAtomNumber_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2332_ = stack[0].m_obj;
lean_object* v_a_2333_ = stack[1].m_obj;
lean_object* v_a_2334_ = stack[2].m_obj;
lean_object* v_a_2335_ = stack[3].m_obj;
lean_object* v_a_2336_ = stack[4].m_obj;
lean_object* v_a_2337_ = stack[5].m_obj;
lean_object* v_a_2338_ = stack[6].m_obj;
lean_object* v_a_2339_ = stack[7].m_obj;
lean_object* v_a_2340_ = stack[8].m_obj;
lean_object* v_a_2341_ = stack[9].m_obj;
lean_object* v_a_2342_ = stack[10].m_obj;
lean_object* v_a_2343_ = stack[11].m_obj;
lean_object* v_res_2346_;
v_res_2346_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_getAtomNumber(v_e_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_);
stack->m_obj
 = v_res_2346_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_getAtomNumber___boxed(lean_object* v_e_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_){
_start:
{
lean_object* v_res_2360_; 
v_res_2360_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_getAtomNumber(v_e_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
lean_dec(v_a_2356_);
lean_dec_ref(v_a_2355_);
lean_dec(v_a_2354_);
lean_dec_ref(v_a_2353_);
lean_dec(v_a_2352_);
lean_dec_ref(v_a_2351_);
lean_dec(v_a_2350_);
lean_dec(v_a_2349_);
lean_dec_ref(v_a_2348_);
lean_dec_ref(v_e_2347_);
return v_res_2360_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2361_; 
v___x_2361_ = l_instMonadEIO___redArg();
return v___x_2361_;
}
}
lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1(lean_object* v_msg_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v_toApplicative_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2449_; 
v___x_2379_ = lean_obj_once(&l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___closed__0, &l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___closed__0_once, _init_l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___closed__0);
v___x_2380_ = l_StateRefT_x27_instMonad___redArg(v___x_2379_);
v_toApplicative_2381_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2449_ == 0)
{
lean_object* v_unused_2450_; 
v_unused_2450_ = lean_ctor_get(v___x_2380_, 1);
lean_dec(v_unused_2450_);
v___x_2383_ = v___x_2380_;
v_isShared_2384_ = v_isSharedCheck_2449_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_toApplicative_2381_);
lean_dec(v___x_2380_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2449_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v_toFunctor_2385_; lean_object* v_toSeq_2386_; lean_object* v_toSeqLeft_2387_; lean_object* v_toSeqRight_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2447_; 
v_toFunctor_2385_ = lean_ctor_get(v_toApplicative_2381_, 0);
v_toSeq_2386_ = lean_ctor_get(v_toApplicative_2381_, 2);
v_toSeqLeft_2387_ = lean_ctor_get(v_toApplicative_2381_, 3);
v_toSeqRight_2388_ = lean_ctor_get(v_toApplicative_2381_, 4);
v_isSharedCheck_2447_ = !lean_is_exclusive(v_toApplicative_2381_);
if (v_isSharedCheck_2447_ == 0)
{
lean_object* v_unused_2448_; 
v_unused_2448_ = lean_ctor_get(v_toApplicative_2381_, 1);
lean_dec(v_unused_2448_);
v___x_2390_ = v_toApplicative_2381_;
v_isShared_2391_ = v_isSharedCheck_2447_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_toSeqRight_2388_);
lean_inc(v_toSeqLeft_2387_);
lean_inc(v_toSeq_2386_);
lean_inc(v_toFunctor_2385_);
lean_dec(v_toApplicative_2381_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2447_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___f_2392_; lean_object* v___f_2393_; lean_object* v___f_2394_; lean_object* v___f_2395_; lean_object* v___x_2396_; lean_object* v___f_2397_; lean_object* v___f_2398_; lean_object* v___f_2399_; lean_object* v___x_2401_; 
v___f_2392_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___closed__1));
v___f_2393_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___closed__2));
lean_inc_ref(v_toFunctor_2385_);
v___f_2394_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2394_, 0, v_toFunctor_2385_);
v___f_2395_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2395_, 0, v_toFunctor_2385_);
v___x_2396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___f_2394_);
lean_ctor_set(v___x_2396_, 1, v___f_2395_);
v___f_2397_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2397_, 0, v_toSeqRight_2388_);
v___f_2398_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2398_, 0, v_toSeqLeft_2387_);
v___f_2399_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2399_, 0, v_toSeq_2386_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 4, v___f_2397_);
lean_ctor_set(v___x_2390_, 3, v___f_2398_);
lean_ctor_set(v___x_2390_, 2, v___f_2399_);
lean_ctor_set(v___x_2390_, 1, v___f_2392_);
lean_ctor_set(v___x_2390_, 0, v___x_2396_);
v___x_2401_ = v___x_2390_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v___x_2396_);
lean_ctor_set(v_reuseFailAlloc_2446_, 1, v___f_2392_);
lean_ctor_set(v_reuseFailAlloc_2446_, 2, v___f_2399_);
lean_ctor_set(v_reuseFailAlloc_2446_, 3, v___f_2398_);
lean_ctor_set(v_reuseFailAlloc_2446_, 4, v___f_2397_);
v___x_2401_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
lean_object* v___x_2403_; 
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 1, v___f_2393_);
lean_ctor_set(v___x_2383_, 0, v___x_2401_);
v___x_2403_ = v___x_2383_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2445_; 
v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2445_, 0, v___x_2401_);
lean_ctor_set(v_reuseFailAlloc_2445_, 1, v___f_2393_);
v___x_2403_ = v_reuseFailAlloc_2445_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
lean_object* v___x_2404_; lean_object* v_toApplicative_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2443_; 
v___x_2404_ = l_StateRefT_x27_instMonad___redArg(v___x_2403_);
v_toApplicative_2405_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2443_ == 0)
{
lean_object* v_unused_2444_; 
v_unused_2444_ = lean_ctor_get(v___x_2404_, 1);
lean_dec(v_unused_2444_);
v___x_2407_ = v___x_2404_;
v_isShared_2408_ = v_isSharedCheck_2443_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_toApplicative_2405_);
lean_dec(v___x_2404_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2443_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v_toFunctor_2409_; lean_object* v_toSeq_2410_; lean_object* v_toSeqLeft_2411_; lean_object* v_toSeqRight_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2441_; 
v_toFunctor_2409_ = lean_ctor_get(v_toApplicative_2405_, 0);
v_toSeq_2410_ = lean_ctor_get(v_toApplicative_2405_, 2);
v_toSeqLeft_2411_ = lean_ctor_get(v_toApplicative_2405_, 3);
v_toSeqRight_2412_ = lean_ctor_get(v_toApplicative_2405_, 4);
v_isSharedCheck_2441_ = !lean_is_exclusive(v_toApplicative_2405_);
if (v_isSharedCheck_2441_ == 0)
{
lean_object* v_unused_2442_; 
v_unused_2442_ = lean_ctor_get(v_toApplicative_2405_, 1);
lean_dec(v_unused_2442_);
v___x_2414_ = v_toApplicative_2405_;
v_isShared_2415_ = v_isSharedCheck_2441_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_toSeqRight_2412_);
lean_inc(v_toSeqLeft_2411_);
lean_inc(v_toSeq_2410_);
lean_inc(v_toFunctor_2409_);
lean_dec(v_toApplicative_2405_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2441_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___f_2416_; lean_object* v___f_2417_; lean_object* v___f_2418_; lean_object* v___f_2419_; lean_object* v___x_2420_; lean_object* v___f_2421_; lean_object* v___f_2422_; lean_object* v___f_2423_; lean_object* v___x_2425_; 
v___f_2416_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___closed__3));
v___f_2417_ = ((lean_object*)(l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___closed__4));
lean_inc_ref(v_toFunctor_2409_);
v___f_2418_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2418_, 0, v_toFunctor_2409_);
v___f_2419_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2419_, 0, v_toFunctor_2409_);
v___x_2420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2420_, 0, v___f_2418_);
lean_ctor_set(v___x_2420_, 1, v___f_2419_);
v___f_2421_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2421_, 0, v_toSeqRight_2412_);
v___f_2422_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2422_, 0, v_toSeqLeft_2411_);
v___f_2423_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2423_, 0, v_toSeq_2410_);
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 4, v___f_2421_);
lean_ctor_set(v___x_2414_, 3, v___f_2422_);
lean_ctor_set(v___x_2414_, 2, v___f_2423_);
lean_ctor_set(v___x_2414_, 1, v___f_2416_);
lean_ctor_set(v___x_2414_, 0, v___x_2420_);
v___x_2425_ = v___x_2414_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2420_);
lean_ctor_set(v_reuseFailAlloc_2440_, 1, v___f_2416_);
lean_ctor_set(v_reuseFailAlloc_2440_, 2, v___f_2423_);
lean_ctor_set(v_reuseFailAlloc_2440_, 3, v___f_2422_);
lean_ctor_set(v_reuseFailAlloc_2440_, 4, v___f_2421_);
v___x_2425_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
lean_object* v___x_2427_; 
if (v_isShared_2408_ == 0)
{
lean_ctor_set(v___x_2407_, 1, v___f_2417_);
lean_ctor_set(v___x_2407_, 0, v___x_2425_);
v___x_2427_ = v___x_2407_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2425_);
lean_ctor_set(v_reuseFailAlloc_2439_, 1, v___f_2417_);
v___x_2427_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___f_2436_; lean_object* v___x_20328__overap_2437_; lean_object* v___x_2438_; 
v___x_2428_ = l_StateRefT_x27_instMonad___redArg(v___x_2427_);
v___x_2429_ = l_ReaderT_instMonad___redArg(v___x_2428_);
v___x_2430_ = l_StateRefT_x27_instMonad___redArg(v___x_2429_);
v___x_2431_ = l_ReaderT_instMonad___redArg(v___x_2430_);
v___x_2432_ = l_ReaderT_instMonad___redArg(v___x_2431_);
v___x_2433_ = l_StateRefT_x27_instMonad___redArg(v___x_2432_);
v___x_2434_ = lean_box(0);
v___x_2435_ = l_instInhabitedOfMonad___redArg(v___x_2433_, v___x_2434_);
v___f_2436_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2436_, 0, v___x_2435_);
v___x_20328__overap_2437_ = lean_panic_fn_borrowed(v___f_2436_, v_msg_2366_);
lean_dec_ref(v___f_2436_);
lean_inc(v___y_2377_);
lean_inc_ref(v___y_2376_);
lean_inc(v___y_2375_);
lean_inc_ref(v___y_2374_);
lean_inc(v___y_2373_);
lean_inc_ref(v___y_2372_);
lean_inc(v___y_2371_);
lean_inc_ref(v___y_2370_);
lean_inc(v___y_2369_);
lean_inc(v___y_2368_);
lean_inc_ref(v___y_2367_);
v___x_2438_ = lean_apply_12(v___x_20328__overap_2437_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, lean_box(0));
return v___x_2438_;
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
LEAN_EXPORT void l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2366_ = stack[0].m_obj;
lean_object* v___y_2367_ = stack[1].m_obj;
lean_object* v___y_2368_ = stack[2].m_obj;
lean_object* v___y_2369_ = stack[3].m_obj;
lean_object* v___y_2370_ = stack[4].m_obj;
lean_object* v___y_2371_ = stack[5].m_obj;
lean_object* v___y_2372_ = stack[6].m_obj;
lean_object* v___y_2373_ = stack[7].m_obj;
lean_object* v___y_2374_ = stack[8].m_obj;
lean_object* v___y_2375_ = stack[9].m_obj;
lean_object* v___y_2376_ = stack[10].m_obj;
lean_object* v___y_2377_ = stack[11].m_obj;
lean_object* v_res_2451_;
v_res_2451_ = l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1(v_msg_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
stack->m_obj
 = v_res_2451_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1___boxed(lean_object* v_msg_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1(v_msg_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v___y_2455_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
return v_res_2465_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_2466_; double v___x_2467_; 
v___x_2466_ = lean_unsigned_to_nat(0u);
v___x_2467_ = lean_float_of_nat(v___x_2466_);
return v___x_2467_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg(lean_object* v_cls_2471_, lean_object* v_msg_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v_ref_2478_; lean_object* v___x_2479_; lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2525_; 
v_ref_2478_ = lean_ctor_get(v___y_2475_, 2);
v___x_2479_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_BVDecide_Reflect_Basic_0__Lean_Meta_Tactic_BVDecide_ReifyM_atomsAssignmentExpr_updateAtomsAssignment_spec__0_spec__0(v_msg_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_);
v_a_2480_ = lean_ctor_get(v___x_2479_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2479_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2482_ = v___x_2479_;
v_isShared_2483_ = v_isSharedCheck_2525_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2479_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2525_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2484_; lean_object* v_traceState_2485_; lean_object* v_env_2486_; lean_object* v_nextMacroScope_2487_; lean_object* v_ngen_2488_; lean_object* v_auxDeclNGen_2489_; lean_object* v_cache_2490_; lean_object* v_recordedDeps_2491_; lean_object* v_messages_2492_; lean_object* v_infoState_2493_; lean_object* v_snapshotTasks_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2524_; 
v___x_2484_ = lean_st_ref_take(v___y_2476_);
v_traceState_2485_ = lean_ctor_get(v___x_2484_, 4);
v_env_2486_ = lean_ctor_get(v___x_2484_, 0);
v_nextMacroScope_2487_ = lean_ctor_get(v___x_2484_, 1);
v_ngen_2488_ = lean_ctor_get(v___x_2484_, 2);
v_auxDeclNGen_2489_ = lean_ctor_get(v___x_2484_, 3);
v_cache_2490_ = lean_ctor_get(v___x_2484_, 5);
v_recordedDeps_2491_ = lean_ctor_get(v___x_2484_, 6);
v_messages_2492_ = lean_ctor_get(v___x_2484_, 7);
v_infoState_2493_ = lean_ctor_get(v___x_2484_, 8);
v_snapshotTasks_2494_ = lean_ctor_get(v___x_2484_, 9);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2496_ = v___x_2484_;
v_isShared_2497_ = v_isSharedCheck_2524_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_snapshotTasks_2494_);
lean_inc(v_infoState_2493_);
lean_inc(v_messages_2492_);
lean_inc(v_recordedDeps_2491_);
lean_inc(v_cache_2490_);
lean_inc(v_traceState_2485_);
lean_inc(v_auxDeclNGen_2489_);
lean_inc(v_ngen_2488_);
lean_inc(v_nextMacroScope_2487_);
lean_inc(v_env_2486_);
lean_dec(v___x_2484_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2524_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
uint64_t v_tid_2498_; lean_object* v_traces_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2523_; 
v_tid_2498_ = lean_ctor_get_uint64(v_traceState_2485_, sizeof(void*)*1);
v_traces_2499_ = lean_ctor_get(v_traceState_2485_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v_traceState_2485_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2501_ = v_traceState_2485_;
v_isShared_2502_ = v_isSharedCheck_2523_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_traces_2499_);
lean_dec(v_traceState_2485_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2523_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; double v___x_2505_; uint8_t v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2514_; 
v___x_2503_ = lean_box(0);
v___x_2504_ = lean_box(0);
v___x_2505_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg___closed__0);
v___x_2506_ = 0;
v___x_2507_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg___closed__1));
v___x_2508_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2508_, 0, v_cls_2471_);
lean_ctor_set(v___x_2508_, 1, v___x_2504_);
lean_ctor_set(v___x_2508_, 2, v___x_2507_);
lean_ctor_set_float(v___x_2508_, sizeof(void*)*3, v___x_2505_);
lean_ctor_set_float(v___x_2508_, sizeof(void*)*3 + 8, v___x_2505_);
lean_ctor_set_uint8(v___x_2508_, sizeof(void*)*3 + 16, v___x_2506_);
v___x_2509_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg___closed__2));
v___x_2510_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2508_);
lean_ctor_set(v___x_2510_, 1, v_a_2480_);
lean_ctor_set(v___x_2510_, 2, v___x_2509_);
lean_inc(v_ref_2478_);
v___x_2511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2511_, 0, v_ref_2478_);
lean_ctor_set(v___x_2511_, 1, v___x_2510_);
v___x_2512_ = l_Lean_PersistentArray_push___redArg(v_traces_2499_, v___x_2511_);
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 0, v___x_2512_);
v___x_2514_ = v___x_2501_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2512_);
lean_ctor_set_uint64(v_reuseFailAlloc_2522_, sizeof(void*)*1, v_tid_2498_);
v___x_2514_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
lean_object* v___x_2516_; 
if (v_isShared_2497_ == 0)
{
lean_ctor_set(v___x_2496_, 4, v___x_2514_);
v___x_2516_ = v___x_2496_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_env_2486_);
lean_ctor_set(v_reuseFailAlloc_2521_, 1, v_nextMacroScope_2487_);
lean_ctor_set(v_reuseFailAlloc_2521_, 2, v_ngen_2488_);
lean_ctor_set(v_reuseFailAlloc_2521_, 3, v_auxDeclNGen_2489_);
lean_ctor_set(v_reuseFailAlloc_2521_, 4, v___x_2514_);
lean_ctor_set(v_reuseFailAlloc_2521_, 5, v_cache_2490_);
lean_ctor_set(v_reuseFailAlloc_2521_, 6, v_recordedDeps_2491_);
lean_ctor_set(v_reuseFailAlloc_2521_, 7, v_messages_2492_);
lean_ctor_set(v_reuseFailAlloc_2521_, 8, v_infoState_2493_);
lean_ctor_set(v_reuseFailAlloc_2521_, 9, v_snapshotTasks_2494_);
v___x_2516_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
lean_object* v___x_2517_; lean_object* v___x_2519_; 
v___x_2517_ = lean_st_ref_put(v___y_2476_, v___x_2516_);
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 0, v___x_2503_);
v___x_2519_ = v___x_2482_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v___x_2503_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2471_ = stack[0].m_obj;
lean_object* v_msg_2472_ = stack[1].m_obj;
lean_object* v___y_2473_ = stack[2].m_obj;
lean_object* v___y_2474_ = stack[3].m_obj;
lean_object* v___y_2475_ = stack[4].m_obj;
lean_object* v___y_2476_ = stack[5].m_obj;
lean_object* v_res_2526_;
v_res_2526_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg(v_cls_2471_, v_msg_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_);
stack->m_obj
 = v_res_2526_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg___boxed(lean_object* v_cls_2527_, lean_object* v_msg_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg(v_cls_2527_, v_msg_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
return v_res_2534_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__5(void){
_start:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2544_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__2));
v___x_2545_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__4));
v___x_2546_ = l_Lean_Name_append(v___x_2545_, v___x_2544_);
return v___x_2546_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__7(void){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2548_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__6));
v___x_2549_ = l_Lean_stringToMessageData(v___x_2548_);
return v___x_2549_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__9(void){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__8));
v___x_2552_ = l_Lean_stringToMessageData(v___x_2551_);
return v___x_2552_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__11(void){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__10));
v___x_2555_ = l_Lean_stringToMessageData(v___x_2554_);
return v___x_2555_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__15(void){
_start:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2559_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__14));
v___x_2560_ = lean_unsigned_to_nat(6u);
v___x_2561_ = lean_unsigned_to_nat(392u);
v___x_2562_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__13));
v___x_2563_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__12));
v___x_2564_ = l_mkPanicMessageWithDecl(v___x_2563_, v___x_2562_, v___x_2561_, v___x_2560_, v___x_2559_);
return v___x_2564_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup(lean_object* v_e_2565_, lean_object* v_width_2566_, uint8_t v_synthetic_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_){
_start:
{
lean_object* v___y_2581_; lean_object* v___x_2602_; lean_object* v_atoms_2603_; lean_object* v___x_2604_; 
v___x_2602_ = lean_st_ref_get(v_a_2569_);
v_atoms_2603_ = lean_ctor_get(v___x_2602_, 0);
lean_inc_ref(v_atoms_2603_);
lean_dec(v___x_2602_);
v___x_2604_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__0___redArg(v_atoms_2603_, v_e_2565_);
lean_dec_ref(v_atoms_2603_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_toCold_2605_; lean_object* v_options_2606_; uint8_t v_hasTrace_2607_; 
v_toCold_2605_ = lean_ctor_get(v_a_2577_, 0);
v_options_2606_ = lean_ctor_get(v_toCold_2605_, 2);
v_hasTrace_2607_ = lean_ctor_get_uint8(v_options_2606_, sizeof(void*)*1);
if (v_hasTrace_2607_ == 0)
{
v___y_2581_ = v_a_2569_;
goto v___jp_2580_;
}
else
{
lean_object* v_inheritedTraceOptions_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; uint8_t v___x_2611_; 
v_inheritedTraceOptions_2608_ = lean_ctor_get(v_toCold_2605_, 11);
v___x_2609_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__2));
v___x_2610_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__5, &l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__5_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__5);
v___x_2611_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2608_, v_options_2606_, v___x_2610_);
if (v___x_2611_ == 0)
{
v___y_2581_ = v_a_2569_;
goto v___jp_2580_;
}
else
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___y_2620_; 
v___x_2612_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__7, &l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__7_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__7);
lean_inc(v_width_2566_);
v___x_2613_ = l_Nat_reprFast(v_width_2566_);
v___x_2614_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2613_);
v___x_2615_ = l_Lean_MessageData_ofFormat(v___x_2614_);
v___x_2616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2612_);
lean_ctor_set(v___x_2616_, 1, v___x_2615_);
v___x_2617_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__9, &l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__9_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__9);
v___x_2618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2616_);
lean_ctor_set(v___x_2618_, 1, v___x_2617_);
if (v_synthetic_2567_ == 0)
{
lean_object* v___x_2637_; 
v___x_2637_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__7));
v___y_2620_ = v___x_2637_;
goto v___jp_2619_;
}
else
{
lean_object* v___x_2638_; 
v___x_2638_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_instToExprBoolExpr_go___redArg___closed__10));
v___y_2620_ = v___x_2638_;
goto v___jp_2619_;
}
v___jp_2619_:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
lean_inc_ref(v___y_2620_);
v___x_2621_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2621_, 0, v___y_2620_);
v___x_2622_ = l_Lean_MessageData_ofFormat(v___x_2621_);
v___x_2623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2618_);
lean_ctor_set(v___x_2623_, 1, v___x_2622_);
v___x_2624_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__11, &l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__11_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__11);
v___x_2625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2623_);
lean_ctor_set(v___x_2625_, 1, v___x_2624_);
lean_inc_ref(v_e_2565_);
v___x_2626_ = l_Lean_MessageData_ofExpr(v_e_2565_);
v___x_2627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2625_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
v___x_2628_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg(v___x_2609_, v___x_2627_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_dec_ref_known(v___x_2628_, 1);
v___y_2581_ = v_a_2569_;
goto v___jp_2580_;
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
lean_dec(v_width_2566_);
lean_dec_ref(v_e_2565_);
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2628_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2628_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
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
}
}
else
{
lean_object* v_val_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2667_; 
lean_dec_ref(v_e_2565_);
v_val_2639_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2641_ = v___x_2604_;
v_isShared_2642_ = v_isSharedCheck_2667_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_val_2639_);
lean_dec(v___x_2604_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2667_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v_width_2643_; lean_object* v_atomNumber_2644_; uint8_t v___x_2645_; 
v_width_2643_ = lean_ctor_get(v_val_2639_, 0);
lean_inc(v_width_2643_);
v_atomNumber_2644_ = lean_ctor_get(v_val_2639_, 1);
lean_inc(v_atomNumber_2644_);
lean_dec(v_val_2639_);
v___x_2645_ = lean_nat_dec_eq(v_width_2566_, v_width_2643_);
lean_dec(v_width_2643_);
lean_dec(v_width_2566_);
if (v___x_2645_ == 0)
{
lean_object* v___x_2646_; lean_object* v___x_2647_; 
lean_del_object(v___x_2641_);
v___x_2646_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__15, &l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__15_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___closed__15);
v___x_2647_ = l_panic___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__1(v___x_2646_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2654_; 
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2654_ == 0)
{
lean_object* v_unused_2655_; 
v_unused_2655_ = lean_ctor_get(v___x_2647_, 0);
lean_dec(v_unused_2655_);
v___x_2649_ = v___x_2647_;
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
else
{
lean_dec(v___x_2647_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2652_; 
if (v_isShared_2650_ == 0)
{
lean_ctor_set(v___x_2649_, 0, v_atomNumber_2644_);
v___x_2652_ = v___x_2649_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_atomNumber_2644_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
else
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2663_; 
lean_dec(v_atomNumber_2644_);
v_a_2656_ = lean_ctor_get(v___x_2647_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2658_ = v___x_2647_;
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2647_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2661_; 
if (v_isShared_2659_ == 0)
{
v___x_2661_ = v___x_2658_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_a_2656_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
}
else
{
lean_object* v___x_2665_; 
if (v_isShared_2642_ == 0)
{
lean_ctor_set_tag(v___x_2641_, 0);
lean_ctor_set(v___x_2641_, 0, v_atomNumber_2644_);
v___x_2665_ = v___x_2641_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_atomNumber_2644_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
v___jp_2580_:
{
lean_object* v___x_2582_; lean_object* v_atoms_2583_; lean_object* v_theoryState_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2598_; 
v___x_2582_ = lean_st_ref_take(v___y_2581_);
v_atoms_2583_ = lean_ctor_get(v___x_2582_, 0);
v_theoryState_2584_ = lean_ctor_get(v___x_2582_, 4);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2598_ == 0)
{
lean_object* v_unused_2599_; lean_object* v_unused_2600_; lean_object* v_unused_2601_; 
v_unused_2599_ = lean_ctor_get(v___x_2582_, 3);
lean_dec(v_unused_2599_);
v_unused_2600_ = lean_ctor_get(v___x_2582_, 2);
lean_dec(v_unused_2600_);
v_unused_2601_ = lean_ctor_get(v___x_2582_, 1);
lean_dec(v_unused_2601_);
v___x_2586_ = v___x_2582_;
v_isShared_2587_ = v_isSharedCheck_2598_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_theoryState_2584_);
lean_inc(v_atoms_2583_);
lean_dec(v___x_2582_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2598_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v_size_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2594_; 
v_size_2588_ = lean_ctor_get(v_atoms_2583_, 0);
lean_inc_n(v_size_2588_, 2);
v___x_2589_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2589_, 0, v_width_2566_);
lean_ctor_set(v___x_2589_, 1, v_size_2588_);
lean_ctor_set_uint8(v___x_2589_, sizeof(void*)*2, v_synthetic_2567_);
v___x_2590_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_BVDecide_ReifiedBVExpr_evalsAtAtoms_spec__1___redArg(v_atoms_2583_, v_e_2565_, v___x_2589_);
v___x_2591_ = lean_box(0);
v___x_2592_ = lean_obj_once(&l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__1, &l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__1_once, _init_l_Lean_Meta_Tactic_BVDecide_ReifyM_run___redArg___closed__1);
if (v_isShared_2587_ == 0)
{
lean_ctor_set(v___x_2586_, 3, v___x_2592_);
lean_ctor_set(v___x_2586_, 2, v___x_2591_);
lean_ctor_set(v___x_2586_, 1, v___x_2591_);
lean_ctor_set(v___x_2586_, 0, v___x_2590_);
v___x_2594_ = v___x_2586_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v___x_2590_);
lean_ctor_set(v_reuseFailAlloc_2597_, 1, v___x_2591_);
lean_ctor_set(v_reuseFailAlloc_2597_, 2, v___x_2591_);
lean_ctor_set(v_reuseFailAlloc_2597_, 3, v___x_2592_);
lean_ctor_set(v_reuseFailAlloc_2597_, 4, v_theoryState_2584_);
v___x_2594_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2595_ = lean_st_ref_put(v___y_2581_, v___x_2594_);
v___x_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2596_, 0, v_size_2588_);
return v___x_2596_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2565_ = stack[0].m_obj;
lean_object* v_width_2566_ = stack[1].m_obj;
uint8_t v_synthetic_2567_ = stack[2].m_num;
lean_object* v_a_2568_ = stack[3].m_obj;
lean_object* v_a_2569_ = stack[4].m_obj;
lean_object* v_a_2570_ = stack[5].m_obj;
lean_object* v_a_2571_ = stack[6].m_obj;
lean_object* v_a_2572_ = stack[7].m_obj;
lean_object* v_a_2573_ = stack[8].m_obj;
lean_object* v_a_2574_ = stack[9].m_obj;
lean_object* v_a_2575_ = stack[10].m_obj;
lean_object* v_a_2576_ = stack[11].m_obj;
lean_object* v_a_2577_ = stack[12].m_obj;
lean_object* v_a_2578_ = stack[13].m_obj;
lean_object* v_res_2668_;
v_res_2668_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup(v_e_2565_, v_width_2566_, v_synthetic_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_);
stack->m_obj
 = v_res_2668_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup___boxed(lean_object* v_e_2669_, lean_object* v_width_2670_, lean_object* v_synthetic_2671_, lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_){
_start:
{
uint8_t v_synthetic_boxed_2684_; lean_object* v_res_2685_; 
v_synthetic_boxed_2684_ = lean_unbox(v_synthetic_2671_);
v_res_2685_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_lookup(v_e_2669_, v_width_2670_, v_synthetic_boxed_2684_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_);
lean_dec(v_a_2682_);
lean_dec_ref(v_a_2681_);
lean_dec(v_a_2680_);
lean_dec_ref(v_a_2679_);
lean_dec(v_a_2678_);
lean_dec_ref(v_a_2677_);
lean_dec(v_a_2676_);
lean_dec_ref(v_a_2675_);
lean_dec(v_a_2674_);
lean_dec(v_a_2673_);
lean_dec_ref(v_a_2672_);
return v_res_2685_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0(lean_object* v_cls_2686_, lean_object* v_msg_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v___x_2700_; 
v___x_2700_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___redArg(v_cls_2686_, v_msg_2687_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
return v___x_2700_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2686_ = stack[0].m_obj;
lean_object* v_msg_2687_ = stack[1].m_obj;
lean_object* v___y_2688_ = stack[2].m_obj;
lean_object* v___y_2689_ = stack[3].m_obj;
lean_object* v___y_2690_ = stack[4].m_obj;
lean_object* v___y_2691_ = stack[5].m_obj;
lean_object* v___y_2692_ = stack[6].m_obj;
lean_object* v___y_2693_ = stack[7].m_obj;
lean_object* v___y_2694_ = stack[8].m_obj;
lean_object* v___y_2695_ = stack[9].m_obj;
lean_object* v___y_2696_ = stack[10].m_obj;
lean_object* v___y_2697_ = stack[11].m_obj;
lean_object* v___y_2698_ = stack[12].m_obj;
lean_object* v_res_2701_;
v_res_2701_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0(v_cls_2686_, v_msg_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
stack->m_obj
 = v_res_2701_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0___boxed(lean_object* v_cls_2702_, lean_object* v_msg_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_BVDecide_ReifyM_lookup_spec__0(v_cls_2702_, v_msg_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
return v_res_2716_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_modifyTheoryState___redArg(lean_object* v_f_2717_, lean_object* v_a_2718_){
_start:
{
lean_object* v___x_2720_; lean_object* v_atoms_2721_; lean_object* v_atomsAssignmentExprCache_2722_; lean_object* v_atomsAssignmentMapCache_2723_; lean_object* v_evalsAtCache_2724_; lean_object* v_theoryState_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2736_; 
v___x_2720_ = lean_st_ref_take(v_a_2718_);
v_atoms_2721_ = lean_ctor_get(v___x_2720_, 0);
v_atomsAssignmentExprCache_2722_ = lean_ctor_get(v___x_2720_, 1);
v_atomsAssignmentMapCache_2723_ = lean_ctor_get(v___x_2720_, 2);
v_evalsAtCache_2724_ = lean_ctor_get(v___x_2720_, 3);
v_theoryState_2725_ = lean_ctor_get(v___x_2720_, 4);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2727_ = v___x_2720_;
v_isShared_2728_ = v_isSharedCheck_2736_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_theoryState_2725_);
lean_inc(v_evalsAtCache_2724_);
lean_inc(v_atomsAssignmentMapCache_2723_);
lean_inc(v_atomsAssignmentExprCache_2722_);
lean_inc(v_atoms_2721_);
lean_dec(v___x_2720_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2736_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2732_; 
v___x_2729_ = lean_box(0);
v___x_2730_ = lean_apply_1(v_f_2717_, v_theoryState_2725_);
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 4, v___x_2730_);
v___x_2732_ = v___x_2727_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v_atoms_2721_);
lean_ctor_set(v_reuseFailAlloc_2735_, 1, v_atomsAssignmentExprCache_2722_);
lean_ctor_set(v_reuseFailAlloc_2735_, 2, v_atomsAssignmentMapCache_2723_);
lean_ctor_set(v_reuseFailAlloc_2735_, 3, v_evalsAtCache_2724_);
lean_ctor_set(v_reuseFailAlloc_2735_, 4, v___x_2730_);
v___x_2732_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2733_ = lean_st_ref_put(v_a_2718_, v___x_2732_);
v___x_2734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2729_);
return v___x_2734_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_ReifyM_modifyTheoryState___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2717_ = stack[0].m_obj;
lean_object* v_a_2718_ = stack[1].m_obj;
lean_object* v_res_2737_;
v_res_2737_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_modifyTheoryState___redArg(v_f_2717_, v_a_2718_);
stack->m_obj
 = v_res_2737_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_modifyTheoryState___redArg___boxed(lean_object* v_f_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_modifyTheoryState___redArg(v_f_2738_, v_a_2739_);
lean_dec(v_a_2739_);
return v_res_2741_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_modifyTheoryState(lean_object* v_f_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_){
_start:
{
lean_object* v___x_2755_; lean_object* v_atoms_2756_; lean_object* v_atomsAssignmentExprCache_2757_; lean_object* v_atomsAssignmentMapCache_2758_; lean_object* v_evalsAtCache_2759_; lean_object* v_theoryState_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2771_; 
v___x_2755_ = lean_st_ref_take(v_a_2744_);
v_atoms_2756_ = lean_ctor_get(v___x_2755_, 0);
v_atomsAssignmentExprCache_2757_ = lean_ctor_get(v___x_2755_, 1);
v_atomsAssignmentMapCache_2758_ = lean_ctor_get(v___x_2755_, 2);
v_evalsAtCache_2759_ = lean_ctor_get(v___x_2755_, 3);
v_theoryState_2760_ = lean_ctor_get(v___x_2755_, 4);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2762_ = v___x_2755_;
v_isShared_2763_ = v_isSharedCheck_2771_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_theoryState_2760_);
lean_inc(v_evalsAtCache_2759_);
lean_inc(v_atomsAssignmentMapCache_2758_);
lean_inc(v_atomsAssignmentExprCache_2757_);
lean_inc(v_atoms_2756_);
lean_dec(v___x_2755_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2771_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2767_; 
v___x_2764_ = lean_box(0);
v___x_2765_ = lean_apply_1(v_f_2742_, v_theoryState_2760_);
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 4, v___x_2765_);
v___x_2767_ = v___x_2762_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_atoms_2756_);
lean_ctor_set(v_reuseFailAlloc_2770_, 1, v_atomsAssignmentExprCache_2757_);
lean_ctor_set(v_reuseFailAlloc_2770_, 2, v_atomsAssignmentMapCache_2758_);
lean_ctor_set(v_reuseFailAlloc_2770_, 3, v_evalsAtCache_2759_);
lean_ctor_set(v_reuseFailAlloc_2770_, 4, v___x_2765_);
v___x_2767_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2768_ = lean_st_ref_put(v_a_2744_, v___x_2767_);
v___x_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2764_);
return v___x_2769_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_ReifyM_modifyTheoryState_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_2742_ = stack[0].m_obj;
lean_object* v_a_2743_ = stack[1].m_obj;
lean_object* v_a_2744_ = stack[2].m_obj;
lean_object* v_a_2745_ = stack[3].m_obj;
lean_object* v_a_2746_ = stack[4].m_obj;
lean_object* v_a_2747_ = stack[5].m_obj;
lean_object* v_a_2748_ = stack[6].m_obj;
lean_object* v_a_2749_ = stack[7].m_obj;
lean_object* v_a_2750_ = stack[8].m_obj;
lean_object* v_a_2751_ = stack[9].m_obj;
lean_object* v_a_2752_ = stack[10].m_obj;
lean_object* v_a_2753_ = stack[11].m_obj;
lean_object* v_res_2772_;
v_res_2772_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_modifyTheoryState(v_f_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_);
stack->m_obj
 = v_res_2772_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_modifyTheoryState___boxed(lean_object* v_f_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_modifyTheoryState(v_f_2773_, v_a_2774_, v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_);
lean_dec(v_a_2784_);
lean_dec_ref(v_a_2783_);
lean_dec(v_a_2782_);
lean_dec_ref(v_a_2781_);
lean_dec(v_a_2780_);
lean_dec_ref(v_a_2779_);
lean_dec(v_a_2778_);
lean_dec_ref(v_a_2777_);
lean_dec(v_a_2776_);
lean_dec(v_a_2775_);
lean_dec_ref(v_a_2774_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyBinaryProof_x27(lean_object* v_mkFRefl_2787_, lean_object* v_fst_2788_, lean_object* v_fproof_2789_, lean_object* v_mkSRefl_2790_, lean_object* v_snd_2791_, lean_object* v_sproof_2792_){
_start:
{
if (lean_obj_tag(v_fproof_2789_) == 0)
{
lean_dec_ref(v_snd_2791_);
lean_dec_ref(v_mkSRefl_2790_);
if (lean_obj_tag(v_sproof_2792_) == 0)
{
lean_object* v___x_2793_; 
lean_dec_ref(v_fst_2788_);
lean_dec_ref(v_mkFRefl_2787_);
v___x_2793_ = lean_box(0);
return v___x_2793_;
}
else
{
lean_object* v_val_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2803_; 
v_val_2794_ = lean_ctor_get(v_sproof_2792_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v_sproof_2792_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2796_ = v_sproof_2792_;
v_isShared_2797_ = v_isSharedCheck_2803_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_val_2794_);
lean_dec(v_sproof_2792_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2803_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2801_; 
v___x_2798_ = lean_apply_1(v_mkFRefl_2787_, v_fst_2788_);
v___x_2799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2798_);
lean_ctor_set(v___x_2799_, 1, v_val_2794_);
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 0, v___x_2799_);
v___x_2801_ = v___x_2796_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v___x_2799_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
}
}
else
{
lean_dec_ref(v_fst_2788_);
lean_dec_ref(v_mkFRefl_2787_);
if (lean_obj_tag(v_sproof_2792_) == 0)
{
lean_object* v_val_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2813_; 
v_val_2804_ = lean_ctor_get(v_fproof_2789_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v_fproof_2789_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2806_ = v_fproof_2789_;
v_isShared_2807_ = v_isSharedCheck_2813_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_val_2804_);
lean_dec(v_fproof_2789_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2813_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2811_; 
v___x_2808_ = lean_apply_1(v_mkSRefl_2790_, v_snd_2791_);
v___x_2809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2809_, 0, v_val_2804_);
lean_ctor_set(v___x_2809_, 1, v___x_2808_);
if (v_isShared_2807_ == 0)
{
lean_ctor_set(v___x_2806_, 0, v___x_2809_);
v___x_2811_ = v___x_2806_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v___x_2809_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
else
{
lean_object* v_val_2814_; lean_object* v_val_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2823_; 
lean_dec_ref(v_snd_2791_);
lean_dec_ref(v_mkSRefl_2790_);
v_val_2814_ = lean_ctor_get(v_fproof_2789_, 0);
lean_inc(v_val_2814_);
lean_dec_ref_known(v_fproof_2789_, 1);
v_val_2815_ = lean_ctor_get(v_sproof_2792_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v_sproof_2792_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2817_ = v_sproof_2792_;
v_isShared_2818_ = v_isSharedCheck_2823_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_val_2815_);
lean_dec(v_sproof_2792_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2823_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2819_; lean_object* v___x_2821_; 
v___x_2819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2819_, 0, v_val_2814_);
lean_ctor_set(v___x_2819_, 1, v_val_2815_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v___x_2819_);
v___x_2821_ = v___x_2817_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v___x_2819_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyBinaryProof(lean_object* v_mkRefl_2824_, lean_object* v_fst_2825_, lean_object* v_fproof_2826_, lean_object* v_snd_2827_, lean_object* v_sproof_2828_){
_start:
{
lean_object* v___x_2829_; 
lean_inc_ref(v_mkRefl_2824_);
v___x_2829_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyBinaryProof_x27(v_mkRefl_2824_, v_fst_2825_, v_fproof_2826_, v_mkRefl_2824_, v_snd_2827_, v_sproof_2828_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyTernaryProof(lean_object* v_mkRefl_2830_, lean_object* v_fst_2831_, lean_object* v_fproof_2832_, lean_object* v_snd_2833_, lean_object* v_sproof_2834_, lean_object* v_thd_2835_, lean_object* v_tproof_2836_){
_start:
{
if (lean_obj_tag(v_fproof_2832_) == 0)
{
lean_object* v___x_2837_; 
lean_inc_ref_n(v_mkRefl_2830_, 2);
v___x_2837_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyBinaryProof_x27(v_mkRefl_2830_, v_snd_2833_, v_sproof_2834_, v_mkRefl_2830_, v_thd_2835_, v_tproof_2836_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v___x_2838_; 
lean_dec_ref(v_fst_2831_);
lean_dec_ref(v_mkRefl_2830_);
v___x_2838_ = lean_box(0);
return v___x_2838_;
}
else
{
lean_object* v_val_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2848_; 
v_val_2839_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2841_ = v___x_2837_;
v_isShared_2842_ = v_isSharedCheck_2848_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_val_2839_);
lean_dec(v___x_2837_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2848_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2846_; 
v___x_2843_ = lean_apply_1(v_mkRefl_2830_, v_fst_2831_);
v___x_2844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2843_);
lean_ctor_set(v___x_2844_, 1, v_val_2839_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v___x_2844_);
v___x_2846_ = v___x_2841_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v___x_2844_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
}
else
{
lean_object* v_val_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2870_; 
lean_dec_ref(v_fst_2831_);
v_val_2849_ = lean_ctor_get(v_fproof_2832_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v_fproof_2832_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2851_ = v_fproof_2832_;
v_isShared_2852_ = v_isSharedCheck_2870_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_val_2849_);
lean_dec(v_fproof_2832_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2870_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2853_; 
lean_inc_ref(v_thd_2835_);
lean_inc_ref(v_snd_2833_);
lean_inc_ref_n(v_mkRefl_2830_, 2);
v___x_2853_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_simplifyBinaryProof_x27(v_mkRefl_2830_, v_snd_2833_, v_sproof_2834_, v_mkRefl_2830_, v_thd_2835_, v_tproof_2836_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2859_; 
lean_inc_ref(v_mkRefl_2830_);
v___x_2854_ = lean_apply_1(v_mkRefl_2830_, v_snd_2833_);
v___x_2855_ = lean_apply_1(v_mkRefl_2830_, v_thd_2835_);
v___x_2856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2854_);
lean_ctor_set(v___x_2856_, 1, v___x_2855_);
v___x_2857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2857_, 0, v_val_2849_);
lean_ctor_set(v___x_2857_, 1, v___x_2856_);
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 0, v___x_2857_);
v___x_2859_ = v___x_2851_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2857_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
else
{
lean_object* v_val_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2869_; 
lean_del_object(v___x_2851_);
lean_dec_ref(v_thd_2835_);
lean_dec_ref(v_snd_2833_);
lean_dec_ref(v_mkRefl_2830_);
v_val_2861_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2863_ = v___x_2853_;
v_isShared_2864_ = v_isSharedCheck_2869_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_val_2861_);
lean_dec(v___x_2853_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2869_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2865_; lean_object* v___x_2867_; 
v___x_2865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2865_, 0, v_val_2849_);
lean_ctor_set(v___x_2865_, 1, v_val_2861_);
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 0, v___x_2865_);
v___x_2867_ = v___x_2863_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v___x_2865_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
}
}
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_getHyps___redArg(lean_object* v_a_2871_){
_start:
{
lean_object* v_hypotheses_2873_; lean_object* v___x_2874_; 
v_hypotheses_2873_ = lean_ctor_get(v_a_2871_, 0);
lean_inc_ref(v_hypotheses_2873_);
v___x_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2874_, 0, v_hypotheses_2873_);
return v___x_2874_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_ReifyM_getHyps___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2871_ = stack[0].m_obj;
lean_object* v_res_2875_;
v_res_2875_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_getHyps___redArg(v_a_2871_);
stack->m_obj
 = v_res_2875_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_getHyps___redArg___boxed(lean_object* v_a_2876_, lean_object* v_a_2877_){
_start:
{
lean_object* v_res_2878_; 
v_res_2878_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_getHyps___redArg(v_a_2876_);
lean_dec_ref(v_a_2876_);
return v_res_2878_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_getHyps(lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_){
_start:
{
lean_object* v_hypotheses_2891_; lean_object* v___x_2892_; 
v_hypotheses_2891_ = lean_ctor_get(v_a_2879_, 0);
lean_inc_ref(v_hypotheses_2891_);
v___x_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2892_, 0, v_hypotheses_2891_);
return v___x_2892_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_ReifyM_getHyps_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2879_ = stack[0].m_obj;
lean_object* v_a_2880_ = stack[1].m_obj;
lean_object* v_a_2881_ = stack[2].m_obj;
lean_object* v_a_2882_ = stack[3].m_obj;
lean_object* v_a_2883_ = stack[4].m_obj;
lean_object* v_a_2884_ = stack[5].m_obj;
lean_object* v_a_2885_ = stack[6].m_obj;
lean_object* v_a_2886_ = stack[7].m_obj;
lean_object* v_a_2887_ = stack[8].m_obj;
lean_object* v_a_2888_ = stack[9].m_obj;
lean_object* v_a_2889_ = stack[10].m_obj;
lean_object* v_res_2893_;
v_res_2893_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_getHyps(v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_);
stack->m_obj
 = v_res_2893_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_ReifyM_getHyps___boxed(lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l_Lean_Meta_Tactic_BVDecide_ReifyM_getHyps(v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_);
lean_dec(v_a_2904_);
lean_dec_ref(v_a_2903_);
lean_dec(v_a_2902_);
lean_dec_ref(v_a_2901_);
lean_dec(v_a_2900_);
lean_dec_ref(v_a_2899_);
lean_dec(v_a_2898_);
lean_dec_ref(v_a_2897_);
lean_dec(v_a_2896_);
lean_dec(v_a_2895_);
lean_dec_ref(v_a_2894_);
return v_res_2906_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg(lean_object* v_m_2907_, lean_object* v_state_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_, lean_object* v_a_2919_){
_start:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2921_ = lean_st_mk_ref(v_state_2908_);
lean_inc(v_a_2919_);
lean_inc_ref(v_a_2918_);
lean_inc(v_a_2917_);
lean_inc_ref(v_a_2916_);
lean_inc(v_a_2915_);
lean_inc_ref(v_a_2914_);
lean_inc(v_a_2913_);
lean_inc_ref(v_a_2912_);
lean_inc(v_a_2911_);
lean_inc(v_a_2910_);
lean_inc_ref(v_a_2909_);
lean_inc(v___x_2921_);
v___x_2922_ = lean_apply_13(v_m_2907_, v___x_2921_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_, lean_box(0));
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2933_; 
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2925_ = v___x_2922_;
v_isShared_2926_ = v_isSharedCheck_2933_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2922_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2933_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2927_; lean_object* v_lemmas_2928_; lean_object* v___x_2929_; lean_object* v___x_2931_; 
v___x_2927_ = lean_st_ref_get(v___x_2921_);
lean_dec(v___x_2921_);
v_lemmas_2928_ = lean_ctor_get(v___x_2927_, 0);
lean_inc_ref(v_lemmas_2928_);
lean_dec(v___x_2927_);
v___x_2929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2929_, 0, v_a_2923_);
lean_ctor_set(v___x_2929_, 1, v_lemmas_2928_);
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 0, v___x_2929_);
v___x_2931_ = v___x_2925_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v___x_2929_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_dec(v___x_2921_);
v_a_2934_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2922_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2922_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_2907_ = stack[0].m_obj;
lean_object* v_state_2908_ = stack[1].m_obj;
lean_object* v_a_2909_ = stack[2].m_obj;
lean_object* v_a_2910_ = stack[3].m_obj;
lean_object* v_a_2911_ = stack[4].m_obj;
lean_object* v_a_2912_ = stack[5].m_obj;
lean_object* v_a_2913_ = stack[6].m_obj;
lean_object* v_a_2914_ = stack[7].m_obj;
lean_object* v_a_2915_ = stack[8].m_obj;
lean_object* v_a_2916_ = stack[9].m_obj;
lean_object* v_a_2917_ = stack[10].m_obj;
lean_object* v_a_2918_ = stack[11].m_obj;
lean_object* v_a_2919_ = stack[12].m_obj;
lean_object* v_res_2942_;
v_res_2942_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg(v_m_2907_, v_state_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_, v_a_2918_, v_a_2919_);
stack->m_obj
 = v_res_2942_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg___boxed(lean_object* v_m_2943_, lean_object* v_state_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_, lean_object* v_a_2955_, lean_object* v_a_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg(v_m_2943_, v_state_2944_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_);
lean_dec(v_a_2955_);
lean_dec_ref(v_a_2954_);
lean_dec(v_a_2953_);
lean_dec_ref(v_a_2952_);
lean_dec(v_a_2951_);
lean_dec_ref(v_a_2950_);
lean_dec(v_a_2949_);
lean_dec_ref(v_a_2948_);
lean_dec(v_a_2947_);
lean_dec(v_a_2946_);
lean_dec_ref(v_a_2945_);
return v_res_2957_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_run(lean_object* v_00_u03b1_2958_, lean_object* v_m_2959_, lean_object* v_state_2960_, lean_object* v_a_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_, lean_object* v_a_2964_, lean_object* v_a_2965_, lean_object* v_a_2966_, lean_object* v_a_2967_, lean_object* v_a_2968_, lean_object* v_a_2969_, lean_object* v_a_2970_, lean_object* v_a_2971_){
_start:
{
lean_object* v___x_2973_; 
v___x_2973_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_run___redArg(v_m_2959_, v_state_2960_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_);
return v___x_2973_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_LemmaM_run_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_2959_ = stack[1].m_obj;
lean_object* v_state_2960_ = stack[2].m_obj;
lean_object* v_a_2961_ = stack[3].m_obj;
lean_object* v_a_2962_ = stack[4].m_obj;
lean_object* v_a_2963_ = stack[5].m_obj;
lean_object* v_a_2964_ = stack[6].m_obj;
lean_object* v_a_2965_ = stack[7].m_obj;
lean_object* v_a_2966_ = stack[8].m_obj;
lean_object* v_a_2967_ = stack[9].m_obj;
lean_object* v_a_2968_ = stack[10].m_obj;
lean_object* v_a_2969_ = stack[11].m_obj;
lean_object* v_a_2970_ = stack[12].m_obj;
lean_object* v_a_2971_ = stack[13].m_obj;
lean_object* v_res_2974_;
v_res_2974_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_run(lean_box(0), v_m_2959_, v_state_2960_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_, v_a_2966_, v_a_2967_, v_a_2968_, v_a_2969_, v_a_2970_, v_a_2971_);
stack->m_obj
 = v_res_2974_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_run___boxed(lean_object* v_00_u03b1_2975_, lean_object* v_m_2976_, lean_object* v_state_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_run(v_00_u03b1_2975_, v_m_2976_, v_state_2977_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_);
lean_dec(v_a_2988_);
lean_dec_ref(v_a_2987_);
lean_dec(v_a_2986_);
lean_dec_ref(v_a_2985_);
lean_dec(v_a_2984_);
lean_dec_ref(v_a_2983_);
lean_dec(v_a_2982_);
lean_dec_ref(v_a_2981_);
lean_dec(v_a_2980_);
lean_dec(v_a_2979_);
lean_dec_ref(v_a_2978_);
return v_res_2990_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg(lean_object* v_lemma_2991_, lean_object* v_a_2992_){
_start:
{
lean_object* v___x_2994_; lean_object* v_lemmas_2995_; lean_object* v_bvExprCache_2996_; lean_object* v_bvPredCache_2997_; lean_object* v_bvLogicalCache_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3009_; 
v___x_2994_ = lean_st_ref_take(v_a_2992_);
v_lemmas_2995_ = lean_ctor_get(v___x_2994_, 0);
v_bvExprCache_2996_ = lean_ctor_get(v___x_2994_, 1);
v_bvPredCache_2997_ = lean_ctor_get(v___x_2994_, 2);
v_bvLogicalCache_2998_ = lean_ctor_get(v___x_2994_, 3);
v_isSharedCheck_3009_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3009_ == 0)
{
v___x_3000_ = v___x_2994_;
v_isShared_3001_ = v_isSharedCheck_3009_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_bvLogicalCache_2998_);
lean_inc(v_bvPredCache_2997_);
lean_inc(v_bvExprCache_2996_);
lean_inc(v_lemmas_2995_);
lean_dec(v___x_2994_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3009_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3005_; 
v___x_3002_ = lean_box(0);
v___x_3003_ = lean_array_push(v_lemmas_2995_, v_lemma_2991_);
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 0, v___x_3003_);
v___x_3005_ = v___x_3000_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v___x_3003_);
lean_ctor_set(v_reuseFailAlloc_3008_, 1, v_bvExprCache_2996_);
lean_ctor_set(v_reuseFailAlloc_3008_, 2, v_bvPredCache_2997_);
lean_ctor_set(v_reuseFailAlloc_3008_, 3, v_bvLogicalCache_2998_);
v___x_3005_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3006_ = lean_st_ref_put(v_a_2992_, v___x_3005_);
v___x_3007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3002_);
return v___x_3007_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_lemma_2991_ = stack[0].m_obj;
lean_object* v_a_2992_ = stack[1].m_obj;
lean_object* v_res_3010_;
v_res_3010_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg(v_lemma_2991_, v_a_2992_);
stack->m_obj
 = v_res_3010_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg___boxed(lean_object* v_lemma_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_){
_start:
{
lean_object* v_res_3014_; 
v_res_3014_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg(v_lemma_3011_, v_a_3012_);
lean_dec(v_a_3012_);
return v_res_3014_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma(lean_object* v_lemma_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_){
_start:
{
lean_object* v___x_3029_; 
v___x_3029_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___redArg(v_lemma_3015_, v_a_3016_);
return v___x_3029_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma_0interp(lean_interpreter_value* stack)
{
lean_object* v_lemma_3015_ = stack[0].m_obj;
lean_object* v_a_3016_ = stack[1].m_obj;
lean_object* v_a_3017_ = stack[2].m_obj;
lean_object* v_a_3018_ = stack[3].m_obj;
lean_object* v_a_3019_ = stack[4].m_obj;
lean_object* v_a_3020_ = stack[5].m_obj;
lean_object* v_a_3021_ = stack[6].m_obj;
lean_object* v_a_3022_ = stack[7].m_obj;
lean_object* v_a_3023_ = stack[8].m_obj;
lean_object* v_a_3024_ = stack[9].m_obj;
lean_object* v_a_3025_ = stack[10].m_obj;
lean_object* v_a_3026_ = stack[11].m_obj;
lean_object* v_a_3027_ = stack[12].m_obj;
lean_object* v_res_3030_;
v_res_3030_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma(v_lemma_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_);
stack->m_obj
 = v_res_3030_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma___boxed(lean_object* v_lemma_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_addLemma(v_lemma_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_);
lean_dec(v_a_3043_);
lean_dec_ref(v_a_3042_);
lean_dec(v_a_3041_);
lean_dec_ref(v_a_3040_);
lean_dec(v_a_3039_);
lean_dec_ref(v_a_3038_);
lean_dec(v_a_3037_);
lean_dec_ref(v_a_3036_);
lean_dec(v_a_3035_);
lean_dec(v_a_3034_);
lean_dec_ref(v_a_3033_);
lean_dec(v_a_3032_);
return v_res_3045_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas___redArg(lean_object* v_a_3048_){
_start:
{
lean_object* v___x_3050_; lean_object* v_bvExprCache_3051_; lean_object* v_bvPredCache_3052_; lean_object* v_bvLogicalCache_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3064_; 
v___x_3050_ = lean_st_ref_take(v_a_3048_);
v_bvExprCache_3051_ = lean_ctor_get(v___x_3050_, 1);
v_bvPredCache_3052_ = lean_ctor_get(v___x_3050_, 2);
v_bvLogicalCache_3053_ = lean_ctor_get(v___x_3050_, 3);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3064_ == 0)
{
lean_object* v_unused_3065_; 
v_unused_3065_ = lean_ctor_get(v___x_3050_, 0);
lean_dec(v_unused_3065_);
v___x_3055_ = v___x_3050_;
v_isShared_3056_ = v_isSharedCheck_3064_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_bvLogicalCache_3053_);
lean_inc(v_bvPredCache_3052_);
lean_inc(v_bvExprCache_3051_);
lean_dec(v___x_3050_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3064_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3060_; 
v___x_3057_ = lean_box(0);
v___x_3058_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas___redArg___closed__0));
if (v_isShared_3056_ == 0)
{
lean_ctor_set(v___x_3055_, 0, v___x_3058_);
v___x_3060_ = v___x_3055_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v___x_3058_);
lean_ctor_set(v_reuseFailAlloc_3063_, 1, v_bvExprCache_3051_);
lean_ctor_set(v_reuseFailAlloc_3063_, 2, v_bvPredCache_3052_);
lean_ctor_set(v_reuseFailAlloc_3063_, 3, v_bvLogicalCache_3053_);
v___x_3060_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3061_ = lean_st_ref_put(v_a_3048_, v___x_3060_);
v___x_3062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3057_);
return v___x_3062_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3048_ = stack[0].m_obj;
lean_object* v_res_3066_;
v_res_3066_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas___redArg(v_a_3048_);
stack->m_obj
 = v_res_3066_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas___redArg___boxed(lean_object* v_a_3067_, lean_object* v_a_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas___redArg(v_a_3067_);
lean_dec(v_a_3067_);
return v_res_3069_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas(lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_){
_start:
{
lean_object* v___x_3083_; 
v___x_3083_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas___redArg(v_a_3070_);
return v___x_3083_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3070_ = stack[0].m_obj;
lean_object* v_a_3071_ = stack[1].m_obj;
lean_object* v_a_3072_ = stack[2].m_obj;
lean_object* v_a_3073_ = stack[3].m_obj;
lean_object* v_a_3074_ = stack[4].m_obj;
lean_object* v_a_3075_ = stack[5].m_obj;
lean_object* v_a_3076_ = stack[6].m_obj;
lean_object* v_a_3077_ = stack[7].m_obj;
lean_object* v_a_3078_ = stack[8].m_obj;
lean_object* v_a_3079_ = stack[9].m_obj;
lean_object* v_a_3080_ = stack[10].m_obj;
lean_object* v_a_3081_ = stack[11].m_obj;
lean_object* v_res_3084_;
v_res_3084_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas(v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_, v_a_3079_, v_a_3080_, v_a_3081_);
stack->m_obj
 = v_res_3084_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas___boxed(lean_object* v_a_3085_, lean_object* v_a_3086_, lean_object* v_a_3087_, lean_object* v_a_3088_, lean_object* v_a_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_resetLemmas(v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_);
lean_dec(v_a_3096_);
lean_dec_ref(v_a_3095_);
lean_dec(v_a_3094_);
lean_dec_ref(v_a_3093_);
lean_dec(v_a_3092_);
lean_dec_ref(v_a_3091_);
lean_dec(v_a_3090_);
lean_dec_ref(v_a_3089_);
lean_dec(v_a_3088_);
lean_dec(v_a_3087_);
lean_dec_ref(v_a_3086_);
lean_dec(v_a_3085_);
return v_res_3098_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_getLemmas___redArg(lean_object* v_a_3099_){
_start:
{
lean_object* v___x_3101_; lean_object* v_lemmas_3102_; lean_object* v___x_3103_; 
v___x_3101_ = lean_st_ref_get(v_a_3099_);
v_lemmas_3102_ = lean_ctor_get(v___x_3101_, 0);
lean_inc_ref(v_lemmas_3102_);
lean_dec(v___x_3101_);
v___x_3103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3103_, 0, v_lemmas_3102_);
return v___x_3103_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_LemmaM_getLemmas___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3099_ = stack[0].m_obj;
lean_object* v_res_3104_;
v_res_3104_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_getLemmas___redArg(v_a_3099_);
stack->m_obj
 = v_res_3104_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_getLemmas___redArg___boxed(lean_object* v_a_3105_, lean_object* v_a_3106_){
_start:
{
lean_object* v_res_3107_; 
v_res_3107_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_getLemmas___redArg(v_a_3105_);
lean_dec(v_a_3105_);
return v_res_3107_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_getLemmas(lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_){
_start:
{
lean_object* v___x_3121_; 
v___x_3121_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_getLemmas___redArg(v_a_3108_);
return v___x_3121_;
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_LemmaM_getLemmas_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3108_ = stack[0].m_obj;
lean_object* v_a_3109_ = stack[1].m_obj;
lean_object* v_a_3110_ = stack[2].m_obj;
lean_object* v_a_3111_ = stack[3].m_obj;
lean_object* v_a_3112_ = stack[4].m_obj;
lean_object* v_a_3113_ = stack[5].m_obj;
lean_object* v_a_3114_ = stack[6].m_obj;
lean_object* v_a_3115_ = stack[7].m_obj;
lean_object* v_a_3116_ = stack[8].m_obj;
lean_object* v_a_3117_ = stack[9].m_obj;
lean_object* v_a_3118_ = stack[10].m_obj;
lean_object* v_a_3119_ = stack[11].m_obj;
lean_object* v_res_3122_;
v_res_3122_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_getLemmas(v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_);
stack->m_obj
 = v_res_3122_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_getLemmas___boxed(lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_getLemmas(v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_);
lean_dec(v_a_3134_);
lean_dec_ref(v_a_3133_);
lean_dec(v_a_3132_);
lean_dec_ref(v_a_3131_);
lean_dec(v_a_3130_);
lean_dec_ref(v_a_3129_);
lean_dec(v_a_3128_);
lean_dec_ref(v_a_3127_);
lean_dec(v_a_3126_);
lean_dec(v_a_3125_);
lean_dec_ref(v_a_3124_);
lean_dec(v_a_3123_);
return v_res_3136_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache(lean_object* v_e_3139_, lean_object* v_f_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_){
_start:
{
lean_object* v___f_3154_; lean_object* v___f_3155_; lean_object* v___x_3156_; lean_object* v_bvExprCache_3157_; lean_object* v___x_3158_; 
v___f_3154_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__0));
v___f_3155_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__1));
v___x_3156_ = lean_st_ref_get(v_a_3141_);
v_bvExprCache_3157_ = lean_ctor_get(v___x_3156_, 1);
lean_inc_ref(v_bvExprCache_3157_);
lean_dec(v___x_3156_);
lean_inc_ref(v_e_3139_);
v___x_3158_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_3154_, v___f_3155_, v_bvExprCache_3157_, v_e_3139_);
lean_dec_ref(v_bvExprCache_3157_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_object* v___x_3159_; 
lean_inc(v_a_3152_);
lean_inc_ref(v_a_3151_);
lean_inc(v_a_3150_);
lean_inc_ref(v_a_3149_);
lean_inc(v_a_3148_);
lean_inc_ref(v_a_3147_);
lean_inc(v_a_3146_);
lean_inc_ref(v_a_3145_);
lean_inc(v_a_3144_);
lean_inc(v_a_3143_);
lean_inc_ref(v_a_3142_);
lean_inc(v_a_3141_);
lean_inc_ref(v_e_3139_);
v___x_3159_ = lean_apply_14(v_f_3140_, v_e_3139_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_, v_a_3152_, lean_box(0));
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3181_; 
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3162_ = v___x_3159_;
v_isShared_3163_ = v_isSharedCheck_3181_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3159_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3181_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3164_; lean_object* v_lemmas_3165_; lean_object* v_bvExprCache_3166_; lean_object* v_bvPredCache_3167_; lean_object* v_bvLogicalCache_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3180_; 
v___x_3164_ = lean_st_ref_take(v_a_3141_);
v_lemmas_3165_ = lean_ctor_get(v___x_3164_, 0);
v_bvExprCache_3166_ = lean_ctor_get(v___x_3164_, 1);
v_bvPredCache_3167_ = lean_ctor_get(v___x_3164_, 2);
v_bvLogicalCache_3168_ = lean_ctor_get(v___x_3164_, 3);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3170_ = v___x_3164_;
v_isShared_3171_ = v_isSharedCheck_3180_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_bvLogicalCache_3168_);
lean_inc(v_bvPredCache_3167_);
lean_inc(v_bvExprCache_3166_);
lean_inc(v_lemmas_3165_);
lean_dec(v___x_3164_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3180_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3172_; lean_object* v___x_3174_; 
lean_inc(v_a_3160_);
v___x_3172_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_3154_, v___f_3155_, v_bvExprCache_3166_, v_e_3139_, v_a_3160_);
if (v_isShared_3171_ == 0)
{
lean_ctor_set(v___x_3170_, 1, v___x_3172_);
v___x_3174_ = v___x_3170_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_lemmas_3165_);
lean_ctor_set(v_reuseFailAlloc_3179_, 1, v___x_3172_);
lean_ctor_set(v_reuseFailAlloc_3179_, 2, v_bvPredCache_3167_);
lean_ctor_set(v_reuseFailAlloc_3179_, 3, v_bvLogicalCache_3168_);
v___x_3174_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
lean_object* v___x_3175_; lean_object* v___x_3177_; 
v___x_3175_ = lean_st_ref_put(v_a_3141_, v___x_3174_);
if (v_isShared_3163_ == 0)
{
v___x_3177_ = v___x_3162_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_a_3160_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3139_);
return v___x_3159_;
}
}
else
{
lean_object* v_val_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3189_; 
lean_dec_ref(v_f_3140_);
lean_dec_ref(v_e_3139_);
v_val_3182_ = lean_ctor_get(v___x_3158_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3184_ = v___x_3158_;
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_val_3182_);
lean_dec(v___x_3158_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3185_ == 0)
{
lean_ctor_set_tag(v___x_3184_, 0);
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_val_3182_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3139_ = stack[0].m_obj;
lean_object* v_f_3140_ = stack[1].m_obj;
lean_object* v_a_3141_ = stack[2].m_obj;
lean_object* v_a_3142_ = stack[3].m_obj;
lean_object* v_a_3143_ = stack[4].m_obj;
lean_object* v_a_3144_ = stack[5].m_obj;
lean_object* v_a_3145_ = stack[6].m_obj;
lean_object* v_a_3146_ = stack[7].m_obj;
lean_object* v_a_3147_ = stack[8].m_obj;
lean_object* v_a_3148_ = stack[9].m_obj;
lean_object* v_a_3149_ = stack[10].m_obj;
lean_object* v_a_3150_ = stack[11].m_obj;
lean_object* v_a_3151_ = stack[12].m_obj;
lean_object* v_a_3152_ = stack[13].m_obj;
lean_object* v_res_3190_;
v_res_3190_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache(v_e_3139_, v_f_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_, v_a_3148_, v_a_3149_, v_a_3150_, v_a_3151_, v_a_3152_);
stack->m_obj
 = v_res_3190_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___boxed(lean_object* v_e_3191_, lean_object* v_f_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_){
_start:
{
lean_object* v_res_3206_; 
v_res_3206_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache(v_e_3191_, v_f_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_);
lean_dec(v_a_3204_);
lean_dec_ref(v_a_3203_);
lean_dec(v_a_3202_);
lean_dec_ref(v_a_3201_);
lean_dec(v_a_3200_);
lean_dec_ref(v_a_3199_);
lean_dec(v_a_3198_);
lean_dec_ref(v_a_3197_);
lean_dec(v_a_3196_);
lean_dec(v_a_3195_);
lean_dec_ref(v_a_3194_);
lean_dec(v_a_3193_);
return v_res_3206_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache(lean_object* v_e_3207_, lean_object* v_f_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_){
_start:
{
lean_object* v___f_3222_; lean_object* v___f_3223_; lean_object* v___x_3224_; lean_object* v_bvPredCache_3225_; lean_object* v___x_3226_; 
v___f_3222_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__0));
v___f_3223_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__1));
v___x_3224_ = lean_st_ref_get(v_a_3209_);
v_bvPredCache_3225_ = lean_ctor_get(v___x_3224_, 2);
lean_inc_ref(v_bvPredCache_3225_);
lean_dec(v___x_3224_);
lean_inc_ref(v_e_3207_);
v___x_3226_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_3222_, v___f_3223_, v_bvPredCache_3225_, v_e_3207_);
lean_dec_ref(v_bvPredCache_3225_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v___x_3227_; 
lean_inc(v_a_3220_);
lean_inc_ref(v_a_3219_);
lean_inc(v_a_3218_);
lean_inc_ref(v_a_3217_);
lean_inc(v_a_3216_);
lean_inc_ref(v_a_3215_);
lean_inc(v_a_3214_);
lean_inc_ref(v_a_3213_);
lean_inc(v_a_3212_);
lean_inc(v_a_3211_);
lean_inc_ref(v_a_3210_);
lean_inc(v_a_3209_);
lean_inc_ref(v_e_3207_);
v___x_3227_ = lean_apply_14(v_f_3208_, v_e_3207_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, lean_box(0));
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_object* v_a_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3249_; 
v_a_3228_ = lean_ctor_get(v___x_3227_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3230_ = v___x_3227_;
v_isShared_3231_ = v_isSharedCheck_3249_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_a_3228_);
lean_dec(v___x_3227_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3249_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v___x_3232_; lean_object* v_lemmas_3233_; lean_object* v_bvExprCache_3234_; lean_object* v_bvPredCache_3235_; lean_object* v_bvLogicalCache_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3248_; 
v___x_3232_ = lean_st_ref_take(v_a_3209_);
v_lemmas_3233_ = lean_ctor_get(v___x_3232_, 0);
v_bvExprCache_3234_ = lean_ctor_get(v___x_3232_, 1);
v_bvPredCache_3235_ = lean_ctor_get(v___x_3232_, 2);
v_bvLogicalCache_3236_ = lean_ctor_get(v___x_3232_, 3);
v_isSharedCheck_3248_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3238_ = v___x_3232_;
v_isShared_3239_ = v_isSharedCheck_3248_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_bvLogicalCache_3236_);
lean_inc(v_bvPredCache_3235_);
lean_inc(v_bvExprCache_3234_);
lean_inc(v_lemmas_3233_);
lean_dec(v___x_3232_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3248_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3240_; lean_object* v___x_3242_; 
lean_inc(v_a_3228_);
v___x_3240_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_3222_, v___f_3223_, v_bvPredCache_3235_, v_e_3207_, v_a_3228_);
if (v_isShared_3239_ == 0)
{
lean_ctor_set(v___x_3238_, 2, v___x_3240_);
v___x_3242_ = v___x_3238_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_lemmas_3233_);
lean_ctor_set(v_reuseFailAlloc_3247_, 1, v_bvExprCache_3234_);
lean_ctor_set(v_reuseFailAlloc_3247_, 2, v___x_3240_);
lean_ctor_set(v_reuseFailAlloc_3247_, 3, v_bvLogicalCache_3236_);
v___x_3242_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
lean_object* v___x_3243_; lean_object* v___x_3245_; 
v___x_3243_ = lean_st_ref_put(v_a_3209_, v___x_3242_);
if (v_isShared_3231_ == 0)
{
v___x_3245_ = v___x_3230_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3228_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3207_);
return v___x_3227_;
}
}
else
{
lean_object* v_val_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3257_; 
lean_dec_ref(v_f_3208_);
lean_dec_ref(v_e_3207_);
v_val_3250_ = lean_ctor_get(v___x_3226_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3252_ = v___x_3226_;
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_val_3250_);
lean_dec(v___x_3226_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v___x_3255_; 
if (v_isShared_3253_ == 0)
{
lean_ctor_set_tag(v___x_3252_, 0);
v___x_3255_ = v___x_3252_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_val_3250_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3207_ = stack[0].m_obj;
lean_object* v_f_3208_ = stack[1].m_obj;
lean_object* v_a_3209_ = stack[2].m_obj;
lean_object* v_a_3210_ = stack[3].m_obj;
lean_object* v_a_3211_ = stack[4].m_obj;
lean_object* v_a_3212_ = stack[5].m_obj;
lean_object* v_a_3213_ = stack[6].m_obj;
lean_object* v_a_3214_ = stack[7].m_obj;
lean_object* v_a_3215_ = stack[8].m_obj;
lean_object* v_a_3216_ = stack[9].m_obj;
lean_object* v_a_3217_ = stack[10].m_obj;
lean_object* v_a_3218_ = stack[11].m_obj;
lean_object* v_a_3219_ = stack[12].m_obj;
lean_object* v_a_3220_ = stack[13].m_obj;
lean_object* v_res_3258_;
v_res_3258_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache(v_e_3207_, v_f_3208_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_);
stack->m_obj
 = v_res_3258_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache___boxed(lean_object* v_e_3259_, lean_object* v_f_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_){
_start:
{
lean_object* v_res_3274_; 
v_res_3274_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVPredCache(v_e_3259_, v_f_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_);
lean_dec(v_a_3272_);
lean_dec_ref(v_a_3271_);
lean_dec(v_a_3270_);
lean_dec_ref(v_a_3269_);
lean_dec(v_a_3268_);
lean_dec_ref(v_a_3267_);
lean_dec(v_a_3266_);
lean_dec_ref(v_a_3265_);
lean_dec(v_a_3264_);
lean_dec(v_a_3263_);
lean_dec_ref(v_a_3262_);
lean_dec(v_a_3261_);
return v_res_3274_;
}
}
lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache(lean_object* v_e_3275_, lean_object* v_f_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_){
_start:
{
lean_object* v___f_3290_; lean_object* v___f_3291_; lean_object* v___x_3292_; lean_object* v_bvLogicalCache_3293_; lean_object* v___x_3294_; 
v___f_3290_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__0));
v___f_3291_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVExprCache___closed__1));
v___x_3292_ = lean_st_ref_get(v_a_3277_);
v_bvLogicalCache_3293_ = lean_ctor_get(v___x_3292_, 3);
lean_inc_ref(v_bvLogicalCache_3293_);
lean_dec(v___x_3292_);
lean_inc_ref(v_e_3275_);
v___x_3294_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_3290_, v___f_3291_, v_bvLogicalCache_3293_, v_e_3275_);
lean_dec_ref(v_bvLogicalCache_3293_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v___x_3295_; 
lean_inc(v_a_3288_);
lean_inc_ref(v_a_3287_);
lean_inc(v_a_3286_);
lean_inc_ref(v_a_3285_);
lean_inc(v_a_3284_);
lean_inc_ref(v_a_3283_);
lean_inc(v_a_3282_);
lean_inc_ref(v_a_3281_);
lean_inc(v_a_3280_);
lean_inc(v_a_3279_);
lean_inc_ref(v_a_3278_);
lean_inc(v_a_3277_);
lean_inc_ref(v_e_3275_);
v___x_3295_ = lean_apply_14(v_f_3276_, v_e_3275_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, lean_box(0));
if (lean_obj_tag(v___x_3295_) == 0)
{
lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3317_; 
v_a_3296_ = lean_ctor_get(v___x_3295_, 0);
v_isSharedCheck_3317_ = !lean_is_exclusive(v___x_3295_);
if (v_isSharedCheck_3317_ == 0)
{
v___x_3298_ = v___x_3295_;
v_isShared_3299_ = v_isSharedCheck_3317_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_a_3296_);
lean_dec(v___x_3295_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3317_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3300_; lean_object* v_lemmas_3301_; lean_object* v_bvExprCache_3302_; lean_object* v_bvPredCache_3303_; lean_object* v_bvLogicalCache_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3316_; 
v___x_3300_ = lean_st_ref_take(v_a_3277_);
v_lemmas_3301_ = lean_ctor_get(v___x_3300_, 0);
v_bvExprCache_3302_ = lean_ctor_get(v___x_3300_, 1);
v_bvPredCache_3303_ = lean_ctor_get(v___x_3300_, 2);
v_bvLogicalCache_3304_ = lean_ctor_get(v___x_3300_, 3);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3306_ = v___x_3300_;
v_isShared_3307_ = v_isSharedCheck_3316_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_bvLogicalCache_3304_);
lean_inc(v_bvPredCache_3303_);
lean_inc(v_bvExprCache_3302_);
lean_inc(v_lemmas_3301_);
lean_dec(v___x_3300_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3316_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v___x_3308_; lean_object* v___x_3310_; 
lean_inc(v_a_3296_);
v___x_3308_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_3290_, v___f_3291_, v_bvLogicalCache_3304_, v_e_3275_, v_a_3296_);
if (v_isShared_3307_ == 0)
{
lean_ctor_set(v___x_3306_, 3, v___x_3308_);
v___x_3310_ = v___x_3306_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_lemmas_3301_);
lean_ctor_set(v_reuseFailAlloc_3315_, 1, v_bvExprCache_3302_);
lean_ctor_set(v_reuseFailAlloc_3315_, 2, v_bvPredCache_3303_);
lean_ctor_set(v_reuseFailAlloc_3315_, 3, v___x_3308_);
v___x_3310_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
lean_object* v___x_3311_; lean_object* v___x_3313_; 
v___x_3311_ = lean_st_ref_put(v_a_3277_, v___x_3310_);
if (v_isShared_3299_ == 0)
{
v___x_3313_ = v___x_3298_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_a_3296_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_3275_);
return v___x_3295_;
}
}
else
{
lean_object* v_val_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3325_; 
lean_dec_ref(v_f_3276_);
lean_dec_ref(v_e_3275_);
v_val_3318_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3320_ = v___x_3294_;
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_val_3318_);
lean_dec(v___x_3294_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3323_; 
if (v_isShared_3321_ == 0)
{
lean_ctor_set_tag(v___x_3320_, 0);
v___x_3323_ = v___x_3320_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_val_3318_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3275_ = stack[0].m_obj;
lean_object* v_f_3276_ = stack[1].m_obj;
lean_object* v_a_3277_ = stack[2].m_obj;
lean_object* v_a_3278_ = stack[3].m_obj;
lean_object* v_a_3279_ = stack[4].m_obj;
lean_object* v_a_3280_ = stack[5].m_obj;
lean_object* v_a_3281_ = stack[6].m_obj;
lean_object* v_a_3282_ = stack[7].m_obj;
lean_object* v_a_3283_ = stack[8].m_obj;
lean_object* v_a_3284_ = stack[9].m_obj;
lean_object* v_a_3285_ = stack[10].m_obj;
lean_object* v_a_3286_ = stack[11].m_obj;
lean_object* v_a_3287_ = stack[12].m_obj;
lean_object* v_a_3288_ = stack[13].m_obj;
lean_object* v_res_3326_;
v_res_3326_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache(v_e_3275_, v_f_3276_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_);
stack->m_obj
 = v_res_3326_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache___boxed(lean_object* v_e_3327_, lean_object* v_f_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_Meta_Tactic_BVDecide_LemmaM_withBVLogicalCache(v_e_3327_, v_f_3328_, v_a_3329_, v_a_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_);
lean_dec(v_a_3340_);
lean_dec_ref(v_a_3339_);
lean_dec(v_a_3338_);
lean_dec_ref(v_a_3337_);
lean_dec(v_a_3336_);
lean_dec_ref(v_a_3335_);
lean_dec(v_a_3334_);
lean_dec_ref(v_a_3333_);
lean_dec(v_a_3332_);
lean_dec(v_a_3331_);
lean_dec_ref(v_a_3330_);
lean_dec(v_a_3329_);
return v_res_3342_;
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
