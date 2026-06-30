// Lean compiler output
// Module: Lean.Elab.Deriving.Repr
// Imports: public import Lean.Meta.Inductive public import Lean.Elab.Deriving.Basic public import Lean.Elab.Deriving.Util
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getBinderInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_Deriving_mkContext(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_instInhabitedInductiveVal_default;
lean_object* l_Lean_Elab_Deriving_mkHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
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
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_mkStrLit(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_positions(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Syntax_mkNumLit(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkInstanceCmds(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isInductiveCore(lean_object*, lean_object*);
lean_object* l_Lean_Elab_registerDerivingHandler(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Repr"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 59, 131, 233, 62, 241, 250, 220)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explicitBinder"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__5 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__5_value),LEAN_SCALAR_PTR_LITERAL(49, 119, 193, 23, 170, 93, 183, 238)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__7 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__7_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__8 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "prec"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__10 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__10_value;
static lean_once_cell_t l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__10_value),LEAN_SCALAR_PTR_LITERAL(178, 133, 204, 73, 239, 123, 12, 87)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__12 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__12_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__13 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__13_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__14 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__14_value;
static lean_once_cell_t l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__15;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__14_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__16 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__17 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__17_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__18_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__14_value),LEAN_SCALAR_PTR_LITERAL(250, 163, 238, 151, 160, 85, 71, 16)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__18 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__18_value)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__19 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__19_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__19_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__20 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__17_value),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__20_value)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__21 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__21_value;
static lean_once_cell_t l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__23 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__23_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__1;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_++_"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(90, 69, 86, 178, 149, 48, 216, 23)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "++"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__5_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__6_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "\" := \""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__7_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__8_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__10_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__12 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__12_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__13 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__13_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__14 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__14_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Deriving"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(230, 230, 99, 85, 138, 169, 166, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 44, 178, 157, 49, 38, 131, 220)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__18_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__19 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__19_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__21 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__21_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__21_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__22 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__22_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__23 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__23_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__24_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__24 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__24_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__24_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__25 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__25_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__26_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__26_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__26 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__26_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__26_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__27 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__27_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__27_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__28 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__28_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__25_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__28_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__29 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__29_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__22_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__29_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__30 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__30_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__19_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__30_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__31 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__31_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__32 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__32_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Format.group"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Format"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__37 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__37_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__38_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(70, 183, 86, 127, 53, 82, 226, 255)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__38_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__37_value),LEAN_SCALAR_PTR_LITERAL(199, 101, 149, 40, 211, 134, 215, 211)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__38 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__38_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__39_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__39_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__37_value),LEAN_SCALAR_PTR_LITERAL(244, 69, 187, 229, 60, 74, 115, 66)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__39 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__39_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__39_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__40 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__40_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__39_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__41 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__41_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__41_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__42 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__42_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__40_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__42_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__43 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__43_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Format.nest"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__44 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__44_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__45;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "nest"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__46 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__46_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(70, 183, 86, 127, 53, 82, 226, 255)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__47_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__46_value),LEAN_SCALAR_PTR_LITERAL(8, 121, 197, 203, 165, 174, 61, 136)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__47 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__47_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__48_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__48_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__48_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__48_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__46_value),LEAN_SCALAR_PTR_LITERAL(179, 146, 214, 149, 195, 116, 102, 235)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__48 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__48_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__48_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__49 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__49_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__48_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__50 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__50_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__50_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__51 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__51_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__49_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__51_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__52 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__52_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "repr"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__53 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__53_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__54;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__53_value),LEAN_SCALAR_PTR_LITERAL(248, 109, 138, 163, 21, 170, 71, 243)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__55 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__55_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__55_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__56 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__56_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__56_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__57 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__57_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__58 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__58_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__59_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__59_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__59_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__59_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__59_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__59_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__58_value),LEAN_SCALAR_PTR_LITERAL(103, 149, 207, 196, 17, 4, 77, 74)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__59 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__59_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__60 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__60_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "\"_\""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__61 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__61_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "\",\""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Format.line"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "line"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__4_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(70, 183, 86, 127, 53, 82, 226, 255)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(20, 237, 177, 226, 131, 244, 212, 161)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__6_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__6_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(103, 89, 162, 50, 159, 227, 59, 53)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__6_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__7_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__6_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__8_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__9_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__7_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__9_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Format.nil"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(70, 183, 86, 127, 53, 82, 226, 255)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(85, 110, 112, 1, 140, 132, 234, 227)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__3 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(38, 56, 177, 235, 80, 228, 131, 10)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__5 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__4_value)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__7 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__5_value),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__7_value)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__8_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Format.bracket"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__9 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__10;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "bracket"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__11 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(70, 183, 86, 127, 53, 82, 226, 255)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__12_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(174, 48, 2, 244, 180, 197, 18, 79)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__12 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(173, 181, 123, 51, 4, 114, 72, 159)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__14 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__15 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__15_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\"{ \""};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__16 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__16_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\" }\""};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__17 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__17_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "'deriving Repr' failed, unexpected number of fields in structure"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__18 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__18_value;
static lean_once_cell_t l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__19;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__5 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__6 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "reprArg"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__1;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(132, 167, 21, 149, 233, 224, 156, 221)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__3_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__4_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "termMax_prec"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__5_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(47, 22, 118, 206, 137, 233, 43, 182)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__6_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "max_prec"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__7_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "text"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(70, 183, 86, 127, 53, 82, 226, 255)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__1_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 91, 42, 41, 58, 31, 42, 63)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__1_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value_aux_1),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 243, 205, 40, 12, 75, 164, 249)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__3_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Format.text"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__4_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__5;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__2_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__6 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__6_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__7 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__7_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__3_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__7_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__8 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__8_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__9 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__9_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__10 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__10_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__12 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__12_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__14 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__14_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__15 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__15_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__17 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__17_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Repr.addAppParen"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__18 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__18_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__19;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "addAppParen"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__20 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__20_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 59, 131, 233, 62, 241, 250, 220)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__21_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(81, 6, 140, 45, 150, 11, 23, 193)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__21 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__21_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__21_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__22 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__22_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__23 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__23_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__27_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__24 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__24_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__25_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__24_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__25 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__25_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__22_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__25_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__26 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__26_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__19_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__26_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__27 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__27_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__39_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__28 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__28_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__41_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__29 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__29_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__28_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__29_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__30 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__30_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__48_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__31 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__31_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__50_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__32 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__32_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__31_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__32_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__33 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__33_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "termIfThenElse"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__34 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__34_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(225, 209, 193, 165, 165, 31, 104, 198)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__35 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__35_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "if"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__36 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__36_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_≥_"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__37 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__37_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__37_value),LEAN_SCALAR_PTR_LITERAL(58, 65, 30, 214, 7, 203, 184, 211)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__38 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__38_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ">="};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__39 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__39_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__40 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__40_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__41 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__41_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__41_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__42 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__42_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "1"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__43 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__43_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "else"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__44 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__44_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "2"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__45 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__45_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__0_value;
static const lean_array_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 208, 235, 82, 91, 230, 203, 159)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__2_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__3 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__3_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBody(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBody___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__3 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__5 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__5_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__7 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__7_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__8 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__8_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__10 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__10_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__12 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__12_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__13 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__12_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__13_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "no_expose"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__15 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__15_value),LEAN_SCALAR_PTR_LITERAL(211, 61, 129, 110, 227, 154, 234, 3)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__17 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__17_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__18 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__18_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__19 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__19_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__19_value),LEAN_SCALAR_PTR_LITERAL(248, 187, 217, 228, 39, 184, 218, 135)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__21 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__21_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__22 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__22_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__22_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__24 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__24_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__24_value),LEAN_SCALAR_PTR_LITERAL(26, 9, 103, 232, 183, 57, 246, 75)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__26 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__26_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__4_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__26_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27_value;
static lean_once_cell_t l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(70, 183, 86, 127, 53, 82, 226, 255)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__29 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__29_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(137, 92, 60, 211, 158, 173, 173, 178)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__31 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__31_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__30_value)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__32 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__32_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__32_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__33 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__33_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__31_value),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__33_value)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__34 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__34_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__35 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__35_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__35_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__37 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__37_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__38 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__38_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__39 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__39_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__38_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__39_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "partial"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__41 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__41_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__41_value),LEAN_SCALAR_PTR_LITERAL(103, 175, 198, 167, 172, 79, 14, 207)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mutual"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__0 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 205, 8, 5, 164, 77, 17, 1)}};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1_value;
static const lean_string_object l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "end"};
static const lean_object* l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__2 = (const lean_object*)&l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkMutualBlock(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkMutualBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__0(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(195, 196, 35, 37, 101, 57, 52, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__53_value),LEAN_SCALAR_PTR_LITERAL(224, 137, 43, 251, 2, 178, 60, 92)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__3;
static const lean_string_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__0_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__0_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__0_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__1_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__1_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__1_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__2_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__1_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__2_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__2_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__3_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__2_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__3_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__3_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__4_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__3_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__4_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__4_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__5_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__4_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(202, 58, 65, 192, 197, 114, 188, 72)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__5_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__5_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__6_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__5_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(5, 224, 49, 20, 188, 146, 89, 35)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__6_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__6_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__7_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__6_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(208, 160, 169, 100, 58, 75, 239, 18)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__7_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__7_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__8_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__7_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(169, 95, 81, 7, 4, 169, 73, 180)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__8_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__8_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__9_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__8_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(231, 58, 223, 30, 148, 240, 234, 38)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__9_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__9_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__10_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__9_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(225, 21, 194, 109, 33, 15, 109, 4)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__10_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__10_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__11_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__10_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 231, 73, 27, 250, 149, 153)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__11_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__11_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__12_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__12_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__12_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__13_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__11_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__12_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(23, 145, 209, 124, 47, 69, 201, 61)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__13_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__13_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__14_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__14_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__14_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__15_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__13_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__14_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(210, 215, 65, 207, 88, 39, 128, 71)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__15_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__15_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__16_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__15_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__2_value),LEAN_SCALAR_PTR_LITERAL(211, 53, 156, 16, 162, 242, 38, 216)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__16_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__16_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__17_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__16_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(69, 90, 211, 79, 166, 122, 95, 47)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__17_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__17_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__18_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__17_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(43, 134, 118, 68, 66, 204, 66, 159)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__18_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__18_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__19_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__18_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 138, 48, 165, 232, 217, 168, 1)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__19_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__19_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__20_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__19_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1829928117) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(125, 196, 216, 153, 78, 142, 253, 232)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__20_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__20_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__21_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__21_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__21_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__22_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__20_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__21_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(62, 155, 187, 30, 146, 67, 38, 109)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__22_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__22_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__23_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__23_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__23_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__24_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__22_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__23_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(178, 217, 197, 232, 108, 25, 15, 192)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__24_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__24_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__25_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__24_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(139, 0, 128, 151, 4, 60, 211, 133)}};
static const lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__25_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__25_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__10));
v___x_19_ = l_String_toRawSubstring_x27(v___x_18_);
return v___x_19_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__15(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__14));
v___x_25_ = l_String_toRawSubstring_x27(v___x_24_);
return v___x_25_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22(void){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Array_mkArray0(lean_box(0));
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader(lean_object* v_indVal_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_52_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1));
v___x_53_ = lean_unsigned_to_nat(1u);
v___x_54_ = l_Lean_Elab_Deriving_mkHeader(v___x_52_, v___x_53_, v_indVal_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
if (lean_obj_tag(v___x_54_) == 0)
{
lean_object* v_a_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_102_; 
v_a_55_ = lean_ctor_get(v___x_54_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_102_ == 0)
{
v___x_57_ = v___x_54_;
v_isShared_58_ = v_isSharedCheck_102_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_a_55_);
lean_dec(v___x_54_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_102_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v_ref_59_; lean_object* v_quotContext_60_; lean_object* v_currMacroScope_61_; uint8_t v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v_binders_84_; lean_object* v_argNames_85_; lean_object* v_targetNames_86_; lean_object* v_targetType_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_101_; 
v_ref_59_ = lean_ctor_get(v_a_49_, 5);
v_quotContext_60_ = lean_ctor_get(v_a_49_, 10);
v_currMacroScope_61_ = lean_ctor_get(v_a_49_, 11);
v___x_62_ = 0;
v___x_63_ = l_Lean_SourceInfo_fromRef(v_ref_59_, v___x_62_);
v___x_64_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__6));
v___x_65_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__7));
lean_inc_n(v___x_63_, 7);
v___x_66_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_63_);
lean_ctor_set(v___x_66_, 1, v___x_65_);
v___x_67_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_68_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11);
v___x_69_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__12));
lean_inc_n(v_currMacroScope_61_, 2);
lean_inc_n(v_quotContext_60_, 2);
v___x_70_ = l_Lean_addMacroScope(v_quotContext_60_, v___x_69_, v_currMacroScope_61_);
v___x_71_ = lean_box(0);
v___x_72_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_72_, 0, v___x_63_);
lean_ctor_set(v___x_72_, 1, v___x_68_);
lean_ctor_set(v___x_72_, 2, v___x_70_);
lean_ctor_set(v___x_72_, 3, v___x_71_);
v___x_73_ = l_Lean_Syntax_node1(v___x_63_, v___x_67_, v___x_72_);
v___x_74_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__13));
v___x_75_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_63_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__15, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__15_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__15);
v___x_77_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__16));
v___x_78_ = l_Lean_addMacroScope(v_quotContext_60_, v___x_77_, v_currMacroScope_61_);
v___x_79_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__21));
v___x_80_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_80_, 0, v___x_63_);
lean_ctor_set(v___x_80_, 1, v___x_76_);
lean_ctor_set(v___x_80_, 2, v___x_78_);
lean_ctor_set(v___x_80_, 3, v___x_79_);
v___x_81_ = l_Lean_Syntax_node2(v___x_63_, v___x_67_, v___x_75_, v___x_80_);
v___x_82_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22);
v___x_83_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_83_, 0, v___x_63_);
lean_ctor_set(v___x_83_, 1, v___x_67_);
lean_ctor_set(v___x_83_, 2, v___x_82_);
v_binders_84_ = lean_ctor_get(v_a_55_, 0);
v_argNames_85_ = lean_ctor_get(v_a_55_, 1);
v_targetNames_86_ = lean_ctor_get(v_a_55_, 2);
v_targetType_87_ = lean_ctor_get(v_a_55_, 3);
v_isSharedCheck_101_ = !lean_is_exclusive(v_a_55_);
if (v_isSharedCheck_101_ == 0)
{
v___x_89_ = v_a_55_;
v_isShared_90_ = v_isSharedCheck_101_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_targetType_87_);
lean_inc(v_targetNames_86_);
lean_inc(v_argNames_85_);
lean_inc(v_binders_84_);
lean_dec(v_a_55_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_101_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_96_; 
v___x_91_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__23));
lean_inc(v___x_63_);
v___x_92_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_92_, 0, v___x_63_);
lean_ctor_set(v___x_92_, 1, v___x_91_);
v___x_93_ = l_Lean_Syntax_node5(v___x_63_, v___x_64_, v___x_66_, v___x_73_, v___x_81_, v___x_83_, v___x_92_);
v___x_94_ = lean_array_push(v_binders_84_, v___x_93_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_94_);
v___x_96_ = v___x_89_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_94_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v_argNames_85_);
lean_ctor_set(v_reuseFailAlloc_100_, 2, v_targetNames_86_);
lean_ctor_set(v_reuseFailAlloc_100_, 3, v_targetType_87_);
v___x_96_ = v_reuseFailAlloc_100_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
lean_object* v___x_98_; 
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_96_);
v___x_98_ = v___x_57_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
}
else
{
return v___x_54_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprHeader___boxed(lean_object* v_indVal_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_Elab_Deriving_Repr_mkReprHeader(v_indVal_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_);
lean_dec(v_a_109_);
lean_dec_ref(v_a_108_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg___lam__0(lean_object* v_k_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v_b_115_, lean_object* v_c_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v___x_122_; 
lean_inc(v___y_120_);
lean_inc_ref(v___y_119_);
lean_inc(v___y_118_);
lean_inc_ref(v___y_117_);
lean_inc(v___y_114_);
lean_inc_ref(v___y_113_);
v___x_122_ = lean_apply_9(v_k_112_, v_b_115_, v_c_116_, v___y_113_, v___y_114_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, lean_box(0));
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg___lam__0___boxed(lean_object* v_k_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v_b_126_, lean_object* v_c_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg___lam__0(v_k_123_, v___y_124_, v___y_125_, v_b_126_, v_c_127_, v___y_128_, v___y_129_, v___y_130_, v___y_131_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
lean_dec(v___y_129_);
lean_dec_ref(v___y_128_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg(lean_object* v_type_134_, lean_object* v_k_135_, uint8_t v_cleanupAnnotations_136_, uint8_t v_whnfType_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v___f_145_; lean_object* v___x_146_; 
lean_inc(v___y_139_);
lean_inc_ref(v___y_138_);
v___f_145_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_145_, 0, v_k_135_);
lean_closure_set(v___f_145_, 1, v___y_138_);
lean_closure_set(v___f_145_, 2, v___y_139_);
v___x_146_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_134_, v___f_145_, v_cleanupAnnotations_136_, v_whnfType_137_, v___y_140_, v___y_141_, v___y_142_, v___y_143_);
if (lean_obj_tag(v___x_146_) == 0)
{
return v___x_146_;
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
v_a_147_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_146_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_146_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_147_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg___boxed(lean_object* v_type_155_, lean_object* v_k_156_, lean_object* v_cleanupAnnotations_157_, lean_object* v_whnfType_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_166_; uint8_t v_whnfType_boxed_167_; lean_object* v_res_168_; 
v_cleanupAnnotations_boxed_166_ = lean_unbox(v_cleanupAnnotations_157_);
v_whnfType_boxed_167_ = lean_unbox(v_whnfType_158_);
v_res_168_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg(v_type_155_, v_k_156_, v_cleanupAnnotations_boxed_166_, v_whnfType_boxed_167_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4(lean_object* v_00_u03b1_169_, lean_object* v_type_170_, lean_object* v_k_171_, uint8_t v_cleanupAnnotations_172_, uint8_t v_whnfType_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg(v_type_170_, v_k_171_, v_cleanupAnnotations_172_, v_whnfType_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___boxed(lean_object* v_00_u03b1_182_, lean_object* v_type_183_, lean_object* v_k_184_, lean_object* v_cleanupAnnotations_185_, lean_object* v_whnfType_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_194_; uint8_t v_whnfType_boxed_195_; lean_object* v_res_196_; 
v_cleanupAnnotations_boxed_194_ = lean_unbox(v_cleanupAnnotations_185_);
v_whnfType_boxed_195_ = lean_unbox(v_whnfType_186_);
v_res_196_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4(v_00_u03b1_182_, v_type_183_, v_k_184_, v_cleanupAnnotations_boxed_194_, v_whnfType_boxed_195_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
return v_res_196_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = lean_box(1);
v___x_198_ = l_Lean_MessageData_ofFormat(v___x_197_);
return v___x_198_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__3(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__2));
v___x_203_ = l_Lean_MessageData_ofFormat(v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8(lean_object* v_x_204_, lean_object* v_x_205_){
_start:
{
if (lean_obj_tag(v_x_205_) == 0)
{
return v_x_204_;
}
else
{
lean_object* v_head_206_; lean_object* v_tail_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_229_; 
v_head_206_ = lean_ctor_get(v_x_205_, 0);
v_tail_207_ = lean_ctor_get(v_x_205_, 1);
v_isSharedCheck_229_ = !lean_is_exclusive(v_x_205_);
if (v_isSharedCheck_229_ == 0)
{
v___x_209_ = v_x_205_;
v_isShared_210_ = v_isSharedCheck_229_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_tail_207_);
lean_inc(v_head_206_);
lean_dec(v_x_205_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_229_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v_before_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_227_; 
v_before_211_ = lean_ctor_get(v_head_206_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v_head_206_);
if (v_isSharedCheck_227_ == 0)
{
lean_object* v_unused_228_; 
v_unused_228_ = lean_ctor_get(v_head_206_, 1);
lean_dec(v_unused_228_);
v___x_213_ = v_head_206_;
v_isShared_214_ = v_isSharedCheck_227_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_before_211_);
lean_dec(v_head_206_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_227_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_215_; lean_object* v___x_217_; 
v___x_215_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0);
if (v_isShared_214_ == 0)
{
lean_ctor_set_tag(v___x_213_, 7);
lean_ctor_set(v___x_213_, 1, v___x_215_);
lean_ctor_set(v___x_213_, 0, v_x_204_);
v___x_217_ = v___x_213_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_x_204_);
lean_ctor_set(v_reuseFailAlloc_226_, 1, v___x_215_);
v___x_217_ = v_reuseFailAlloc_226_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
lean_object* v___x_218_; lean_object* v___x_220_; 
v___x_218_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__3);
if (v_isShared_210_ == 0)
{
lean_ctor_set_tag(v___x_209_, 7);
lean_ctor_set(v___x_209_, 1, v___x_218_);
lean_ctor_set(v___x_209_, 0, v___x_217_);
v___x_220_ = v___x_209_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_217_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v___x_218_);
v___x_220_ = v_reuseFailAlloc_225_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_221_ = l_Lean_MessageData_ofSyntax(v_before_211_);
v___x_222_ = l_Lean_indentD(v___x_221_);
v___x_223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_220_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v_x_204_ = v___x_223_;
v_x_205_ = v_tail_207_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__7(lean_object* v_opts_230_, lean_object* v_opt_231_){
_start:
{
lean_object* v_name_232_; lean_object* v_defValue_233_; lean_object* v_map_234_; lean_object* v___x_235_; 
v_name_232_ = lean_ctor_get(v_opt_231_, 0);
v_defValue_233_ = lean_ctor_get(v_opt_231_, 1);
v_map_234_ = lean_ctor_get(v_opts_230_, 0);
v___x_235_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_234_, v_name_232_);
if (lean_obj_tag(v___x_235_) == 0)
{
uint8_t v___x_236_; 
v___x_236_ = lean_unbox(v_defValue_233_);
return v___x_236_;
}
else
{
lean_object* v_val_237_; 
v_val_237_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_val_237_);
lean_dec_ref_known(v___x_235_, 1);
if (lean_obj_tag(v_val_237_) == 1)
{
uint8_t v_v_238_; 
v_v_238_ = lean_ctor_get_uint8(v_val_237_, 0);
lean_dec_ref_known(v_val_237_, 0);
return v_v_238_;
}
else
{
uint8_t v___x_239_; 
lean_dec(v_val_237_);
v___x_239_ = lean_unbox(v_defValue_233_);
return v___x_239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__7___boxed(lean_object* v_opts_240_, lean_object* v_opt_241_){
_start:
{
uint8_t v_res_242_; lean_object* v_r_243_; 
v_res_242_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__7(v_opts_240_, v_opt_241_);
lean_dec_ref(v_opt_241_);
lean_dec_ref(v_opts_240_);
v_r_243_ = lean_box(v_res_242_);
return v_r_243_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__1));
v___x_248_ = l_Lean_MessageData_ofFormat(v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg(lean_object* v_msgData_249_, lean_object* v_macroStack_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_options_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v_options_253_ = lean_ctor_get(v___y_251_, 2);
v___x_254_ = l_Lean_Elab_pp_macroStack;
v___x_255_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__7(v_options_253_, v___x_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; 
lean_dec(v_macroStack_250_);
v___x_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_256_, 0, v_msgData_249_);
return v___x_256_;
}
else
{
if (lean_obj_tag(v_macroStack_250_) == 0)
{
lean_object* v___x_257_; 
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v_msgData_249_);
return v___x_257_;
}
else
{
lean_object* v_head_258_; lean_object* v_after_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_274_; 
v_head_258_ = lean_ctor_get(v_macroStack_250_, 0);
lean_inc(v_head_258_);
v_after_259_ = lean_ctor_get(v_head_258_, 1);
v_isSharedCheck_274_ = !lean_is_exclusive(v_head_258_);
if (v_isSharedCheck_274_ == 0)
{
lean_object* v_unused_275_; 
v_unused_275_ = lean_ctor_get(v_head_258_, 0);
lean_dec(v_unused_275_);
v___x_261_ = v_head_258_;
v_isShared_262_ = v_isSharedCheck_274_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_after_259_);
lean_dec(v_head_258_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_274_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; lean_object* v___x_265_; 
v___x_263_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8___closed__0);
if (v_isShared_262_ == 0)
{
lean_ctor_set_tag(v___x_261_, 7);
lean_ctor_set(v___x_261_, 1, v___x_263_);
lean_ctor_set(v___x_261_, 0, v_msgData_249_);
v___x_265_ = v___x_261_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_msgData_249_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v___x_263_);
v___x_265_ = v_reuseFailAlloc_273_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v_msgData_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_266_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___closed__2);
v___x_267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_265_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
v___x_268_ = l_Lean_MessageData_ofSyntax(v_after_259_);
v___x_269_ = l_Lean_indentD(v___x_268_);
v_msgData_270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_270_, 0, v___x_267_);
lean_ctor_set(v_msgData_270_, 1, v___x_269_);
v___x_271_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5_spec__8(v_msgData_270_, v_macroStack_250_);
v___x_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
return v___x_272_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg___boxed(lean_object* v_msgData_276_, lean_object* v_macroStack_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg(v_msgData_276_, v_macroStack_277_, v___y_278_);
lean_dec_ref(v___y_278_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__4(lean_object* v_msgData_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v___x_287_; lean_object* v_env_288_; lean_object* v___x_289_; lean_object* v_mctx_290_; lean_object* v_lctx_291_; lean_object* v_options_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_287_ = lean_st_ref_get(v___y_285_);
v_env_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc_ref(v_env_288_);
lean_dec(v___x_287_);
v___x_289_ = lean_st_ref_get(v___y_283_);
v_mctx_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc_ref(v_mctx_290_);
lean_dec(v___x_289_);
v_lctx_291_ = lean_ctor_get(v___y_282_, 2);
v_options_292_ = lean_ctor_get(v___y_284_, 2);
lean_inc_ref(v_options_292_);
lean_inc_ref(v_lctx_291_);
v___x_293_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_293_, 0, v_env_288_);
lean_ctor_set(v___x_293_, 1, v_mctx_290_);
lean_ctor_set(v___x_293_, 2, v_lctx_291_);
lean_ctor_set(v___x_293_, 3, v_options_292_);
v___x_294_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
lean_ctor_set(v___x_294_, 1, v_msgData_281_);
v___x_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__4___boxed(lean_object* v_msgData_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__4(v_msgData_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg(lean_object* v_msg_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_ref_311_; lean_object* v___x_312_; lean_object* v_a_313_; lean_object* v_macroStack_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_325_; 
v_ref_311_ = lean_ctor_get(v___y_308_, 5);
v___x_312_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__4(v_msg_303_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
v_a_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_a_313_);
lean_dec_ref(v___x_312_);
v_macroStack_314_ = lean_ctor_get(v___y_304_, 1);
v___x_315_ = l_Lean_Elab_getBetterRef(v_ref_311_, v_macroStack_314_);
lean_inc(v_macroStack_314_);
v___x_316_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg(v_a_313_, v_macroStack_314_, v___y_308_);
v_a_317_ = lean_ctor_get(v___x_316_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_316_);
if (v_isSharedCheck_325_ == 0)
{
v___x_319_ = v___x_316_;
v_isShared_320_ = v_isSharedCheck_325_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_316_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_325_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_321_; lean_object* v___x_323_; 
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_315_);
lean_ctor_set(v___x_321_, 1, v_a_317_);
if (v_isShared_320_ == 0)
{
lean_ctor_set_tag(v___x_319_, 1);
lean_ctor_set(v___x_319_, 0, v___x_321_);
v___x_323_ = v___x_319_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v___x_321_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg___boxed(lean_object* v_msg_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg(v_msg_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg(lean_object* v___x_335_, lean_object* v___x_336_, lean_object* v_a_337_, lean_object* v_b_338_){
_start:
{
lean_object* v_startInclusive_339_; lean_object* v_endExclusive_340_; lean_object* v___x_341_; uint8_t v___x_342_; 
v_startInclusive_339_ = lean_ctor_get(v___x_335_, 1);
v_endExclusive_340_ = lean_ctor_get(v___x_335_, 2);
v___x_341_ = lean_nat_sub(v_endExclusive_340_, v_startInclusive_339_);
v___x_342_ = lean_nat_dec_eq(v_a_337_, v___x_341_);
lean_dec(v___x_341_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_343_ = lean_string_utf8_next_fast(v___x_336_, v_a_337_);
lean_dec(v_a_337_);
v___x_344_ = lean_unsigned_to_nat(1u);
v___x_345_ = lean_nat_add(v_b_338_, v___x_344_);
lean_dec(v_b_338_);
v_a_337_ = v___x_343_;
v_b_338_ = v___x_345_;
goto _start;
}
else
{
lean_dec(v_a_337_);
return v_b_338_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg___boxed(lean_object* v___x_347_, lean_object* v___x_348_, lean_object* v_a_349_, lean_object* v_b_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg(v___x_347_, v___x_348_, v_a_349_, v_b_350_);
lean_dec_ref(v___x_348_);
lean_dec_ref(v___x_347_);
return v_res_351_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__0));
v___x_354_ = lean_string_utf8_byte_size(v___x_353_);
return v___x_354_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15(void){
_start:
{
lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_379_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__14));
v___x_380_ = l_String_toRawSubstring_x27(v___x_379_);
return v___x_380_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35(void){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__34));
v___x_427_ = l_String_toRawSubstring_x27(v___x_426_);
return v___x_427_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__45(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__44));
v___x_450_ = l_String_toRawSubstring_x27(v___x_449_);
return v___x_450_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__54(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__53));
v___x_472_ = l_String_toRawSubstring_x27(v___x_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1(lean_object* v___f_489_, lean_object* v___x_490_, lean_object* v___x_491_, lean_object* v___x_492_, lean_object* v___x_493_, lean_object* v___x_494_, lean_object* v___x_495_, lean_object* v___x_496_, lean_object* v_____r_497_, lean_object* v_fields_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v___y_507_; lean_object* v___x_633_; 
lean_inc_ref(v___x_496_);
v___x_633_ = l_Lean_Meta_isType(v___x_496_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v_a_634_; uint8_t v___x_635_; 
v_a_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc(v_a_634_);
v___x_635_ = lean_unbox(v_a_634_);
lean_dec(v_a_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; 
lean_dec_ref_known(v___x_633_, 1);
v___x_636_ = l_Lean_Meta_isProof(v___x_496_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
v___y_507_ = v___x_636_;
goto v___jp_506_;
}
else
{
lean_dec_ref(v___x_496_);
v___y_507_ = v___x_633_;
goto v___jp_506_;
}
}
else
{
lean_dec_ref(v___x_496_);
v___y_507_ = v___x_633_;
goto v___jp_506_;
}
v___jp_506_:
{
if (lean_obj_tag(v___y_507_) == 0)
{
lean_object* v_a_508_; uint8_t v___x_509_; 
v_a_508_ = lean_ctor_get(v___y_507_, 0);
lean_inc(v_a_508_);
lean_dec_ref_known(v___y_507_, 1);
v___x_509_ = lean_unbox(v_a_508_);
lean_dec(v_a_508_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; 
lean_inc(v___y_504_);
lean_inc_ref(v___y_503_);
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
lean_inc(v___y_500_);
lean_inc_ref(v___y_499_);
v___x_510_ = lean_apply_7(v___f_489_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, lean_box(0));
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_585_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_585_ == 0)
{
v___x_513_ = v___x_510_;
v_isShared_514_ = v_isSharedCheck_585_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_510_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_585_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_515_; lean_object* v_quotContext_516_; lean_object* v_currMacroScope_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_583_; 
v___x_515_ = lean_string_utf8_byte_size(v___x_490_);
v_quotContext_516_ = lean_ctor_get(v___y_503_, 10);
v_currMacroScope_517_ = lean_ctor_get(v___y_503_, 11);
lean_inc(v___x_491_);
lean_inc_ref(v___x_490_);
v___x_518_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_518_, 0, v___x_490_);
lean_ctor_set(v___x_518_, 1, v___x_491_);
lean_ctor_set(v___x_518_, 2, v___x_515_);
v___x_519_ = l_String_Slice_positions(v___x_518_);
v___x_520_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg(v___x_518_, v___x_490_, v___x_519_, v___x_491_);
lean_dec_ref(v___x_490_);
lean_dec_ref_known(v___x_518_, 3);
v___x_521_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__1);
v___x_522_ = lean_nat_add(v___x_520_, v___x_521_);
lean_dec(v___x_520_);
v___x_523_ = l_Nat_reprFast(v___x_522_);
v___x_524_ = l_Lean_Syntax_mkNumLit(v___x_523_, v___x_492_);
v___x_525_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__3));
v___x_526_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4));
lean_inc_n(v_a_511_, 25);
v___x_527_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_527_, 0, v_a_511_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
lean_inc_ref_n(v___x_527_, 2);
v___x_528_ = l_Lean_Syntax_node3(v_a_511_, v___x_525_, v_fields_498_, v___x_527_, v___x_493_);
v___x_529_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__6));
v___x_530_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__7));
v___x_531_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_531_, 0, v_a_511_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = l_Lean_Syntax_node1(v_a_511_, v___x_529_, v___x_531_);
v___x_533_ = l_Lean_Syntax_node3(v_a_511_, v___x_525_, v___x_528_, v___x_527_, v___x_532_);
v___x_534_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9));
v___x_535_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11));
v___x_536_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__7));
v___x_537_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_537_, 0, v_a_511_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__13));
v___x_539_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15);
v___x_540_ = lean_box(0);
lean_inc_n(v_currMacroScope_517_, 4);
lean_inc_n(v_quotContext_516_, 4);
v___x_541_ = l_Lean_addMacroScope(v_quotContext_516_, v___x_540_, v_currMacroScope_517_);
v___x_542_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__31));
v___x_543_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_543_, 0, v_a_511_);
lean_ctor_set(v___x_543_, 1, v___x_539_);
lean_ctor_set(v___x_543_, 2, v___x_541_);
lean_ctor_set(v___x_543_, 3, v___x_542_);
v___x_544_ = l_Lean_Syntax_node1(v_a_511_, v___x_538_, v___x_543_);
v___x_545_ = l_Lean_Syntax_node2(v_a_511_, v___x_535_, v___x_537_, v___x_544_);
v___x_546_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33));
v___x_547_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35);
v___x_548_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__38));
v___x_549_ = l_Lean_addMacroScope(v_quotContext_516_, v___x_548_, v_currMacroScope_517_);
v___x_550_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__43));
v___x_551_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_551_, 0, v_a_511_);
lean_ctor_set(v___x_551_, 1, v___x_547_);
lean_ctor_set(v___x_551_, 2, v___x_549_);
lean_ctor_set(v___x_551_, 3, v___x_550_);
v___x_552_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_553_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__45, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__45_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__45);
v___x_554_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__47));
v___x_555_ = l_Lean_addMacroScope(v_quotContext_516_, v___x_554_, v_currMacroScope_517_);
v___x_556_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__52));
v___x_557_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_557_, 0, v_a_511_);
lean_ctor_set(v___x_557_, 1, v___x_553_);
lean_ctor_set(v___x_557_, 2, v___x_555_);
lean_ctor_set(v___x_557_, 3, v___x_556_);
v___x_558_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__54, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__54_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__54);
v___x_559_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__55));
v___x_560_ = l_Lean_addMacroScope(v_quotContext_516_, v___x_559_, v_currMacroScope_517_);
v___x_561_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__57));
v___x_562_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_562_, 0, v_a_511_);
lean_ctor_set(v___x_562_, 1, v___x_558_);
lean_ctor_set(v___x_562_, 2, v___x_560_);
lean_ctor_set(v___x_562_, 3, v___x_561_);
v___x_563_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__59));
v___x_564_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__60));
v___x_565_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_565_, 0, v_a_511_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
v___x_566_ = lean_mk_syntax_ident(v___x_494_);
v___x_567_ = l_Lean_Syntax_node3(v_a_511_, v___x_563_, v___x_495_, v___x_565_, v___x_566_);
v___x_568_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__23));
v___x_569_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_569_, 0, v_a_511_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
lean_inc_ref_n(v___x_569_, 3);
lean_inc_n(v___x_545_, 3);
v___x_570_ = l_Lean_Syntax_node3(v_a_511_, v___x_534_, v___x_545_, v___x_567_, v___x_569_);
v___x_571_ = l_Lean_Syntax_node1(v_a_511_, v___x_552_, v___x_570_);
v___x_572_ = l_Lean_Syntax_node2(v_a_511_, v___x_546_, v___x_562_, v___x_571_);
v___x_573_ = l_Lean_Syntax_node3(v_a_511_, v___x_534_, v___x_545_, v___x_572_, v___x_569_);
v___x_574_ = l_Lean_Syntax_node2(v_a_511_, v___x_552_, v___x_524_, v___x_573_);
v___x_575_ = l_Lean_Syntax_node2(v_a_511_, v___x_546_, v___x_557_, v___x_574_);
v___x_576_ = l_Lean_Syntax_node3(v_a_511_, v___x_534_, v___x_545_, v___x_575_, v___x_569_);
v___x_577_ = l_Lean_Syntax_node1(v_a_511_, v___x_552_, v___x_576_);
v___x_578_ = l_Lean_Syntax_node2(v_a_511_, v___x_546_, v___x_551_, v___x_577_);
v___x_579_ = l_Lean_Syntax_node3(v_a_511_, v___x_534_, v___x_545_, v___x_578_, v___x_569_);
v___x_580_ = l_Lean_Syntax_node3(v_a_511_, v___x_525_, v___x_533_, v___x_527_, v___x_579_);
v___x_581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 0, v___x_581_);
v___x_583_ = v___x_513_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v___x_581_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
else
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
lean_dec(v_fields_498_);
lean_dec(v___x_495_);
lean_dec(v___x_494_);
lean_dec(v___x_493_);
lean_dec(v___x_492_);
lean_dec(v___x_491_);
lean_dec_ref(v___x_490_);
v_a_586_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_510_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_510_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
else
{
lean_object* v___x_594_; 
lean_dec(v___x_495_);
lean_dec(v___x_494_);
lean_dec(v___x_492_);
lean_dec(v___x_491_);
lean_dec_ref(v___x_490_);
lean_inc(v___y_504_);
lean_inc_ref(v___y_503_);
lean_inc(v___y_502_);
lean_inc_ref(v___y_501_);
lean_inc(v___y_500_);
lean_inc_ref(v___y_499_);
v___x_594_ = lean_apply_7(v___f_489_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, lean_box(0));
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_616_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_616_ == 0)
{
v___x_597_ = v___x_594_;
v_isShared_598_ = v_isSharedCheck_616_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_616_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_599_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__3));
v___x_600_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4));
lean_inc_n(v_a_595_, 7);
v___x_601_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_601_, 0, v_a_595_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
lean_inc_ref_n(v___x_601_, 2);
v___x_602_ = l_Lean_Syntax_node3(v_a_595_, v___x_599_, v_fields_498_, v___x_601_, v___x_493_);
v___x_603_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__6));
v___x_604_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__7));
v___x_605_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_605_, 0, v_a_595_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = l_Lean_Syntax_node1(v_a_595_, v___x_603_, v___x_605_);
v___x_607_ = l_Lean_Syntax_node3(v_a_595_, v___x_599_, v___x_602_, v___x_601_, v___x_606_);
v___x_608_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__61));
v___x_609_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_609_, 0, v_a_595_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
v___x_610_ = l_Lean_Syntax_node1(v_a_595_, v___x_603_, v___x_609_);
v___x_611_ = l_Lean_Syntax_node3(v_a_595_, v___x_599_, v___x_607_, v___x_601_, v___x_610_);
v___x_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_612_);
v___x_614_ = v___x_597_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_612_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
else
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
lean_dec(v_fields_498_);
lean_dec(v___x_493_);
v_a_617_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_594_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_594_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec(v_fields_498_);
lean_dec(v___x_495_);
lean_dec(v___x_494_);
lean_dec(v___x_493_);
lean_dec(v___x_492_);
lean_dec(v___x_491_);
lean_dec_ref(v___x_490_);
lean_dec_ref(v___f_489_);
v_a_625_ = lean_ctor_get(v___y_507_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___y_507_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___y_507_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___y_507_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___f_637_ = _args[0];
lean_object* v___x_638_ = _args[1];
lean_object* v___x_639_ = _args[2];
lean_object* v___x_640_ = _args[3];
lean_object* v___x_641_ = _args[4];
lean_object* v___x_642_ = _args[5];
lean_object* v___x_643_ = _args[6];
lean_object* v___x_644_ = _args[7];
lean_object* v_____r_645_ = _args[8];
lean_object* v_fields_646_ = _args[9];
lean_object* v___y_647_ = _args[10];
lean_object* v___y_648_ = _args[11];
lean_object* v___y_649_ = _args[12];
lean_object* v___y_650_ = _args[13];
lean_object* v___y_651_ = _args[14];
lean_object* v___y_652_ = _args[15];
lean_object* v___y_653_ = _args[16];
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1(v___f_637_, v___x_638_, v___x_639_, v___x_640_, v___x_641_, v___x_642_, v___x_643_, v___x_644_, v_____r_645_, v_fields_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__0(lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v_ref_662_; uint8_t v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v_ref_662_ = lean_ctor_get(v___y_659_, 5);
v___x_663_ = 0;
v___x_664_ = l_Lean_SourceInfo_fromRef(v_ref_662_, v___x_663_);
v___x_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__0___boxed(lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__0(v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v___y_666_);
return v_res_673_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__2));
v___x_678_ = l_String_toRawSubstring_x27(v___x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg(lean_object* v_upperBound_698_, lean_object* v___x_699_, lean_object* v___x_700_, lean_object* v_xs_701_, lean_object* v___x_702_, lean_object* v_a_703_, lean_object* v_b_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v___y_713_; uint8_t v___x_735_; 
v___x_735_ = lean_nat_dec_lt(v_a_703_, v_upperBound_698_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; 
lean_dec(v_a_703_);
lean_dec(v___x_702_);
v___x_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_736_, 0, v_b_704_);
return v___x_736_;
}
else
{
lean_object* v___f_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; uint8_t v___x_746_; 
v___f_737_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__0));
v___x_738_ = l_Lean_instInhabitedExpr;
v___x_739_ = lean_unsigned_to_nat(0u);
v___x_740_ = lean_array_fget_borrowed(v___x_699_, v_a_703_);
lean_inc(v___x_740_);
v___x_741_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_740_, v___x_735_);
v___x_742_ = lean_box(2);
lean_inc_ref(v___x_741_);
v___x_743_ = l_Lean_Syntax_mkStrLit(v___x_741_, v___x_742_);
v___x_744_ = lean_nat_add(v___x_700_, v_a_703_);
v___x_745_ = lean_array_get_borrowed(v___x_738_, v_xs_701_, v___x_744_);
lean_dec(v___x_744_);
v___x_746_ = lean_nat_dec_eq(v_a_703_, v___x_739_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; 
v___x_747_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__0(v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v_quotContext_749_; lean_object* v_currMacroScope_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc_n(v_a_748_, 6);
lean_dec_ref_known(v___x_747_, 1);
v_quotContext_749_ = lean_ctor_get(v___y_709_, 10);
v_currMacroScope_750_ = lean_ctor_get(v___y_709_, 11);
v___x_751_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__3));
v___x_752_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4));
v___x_753_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_753_, 0, v_a_748_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__6));
v___x_755_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__1));
v___x_756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_756_, 0, v_a_748_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = l_Lean_Syntax_node1(v_a_748_, v___x_754_, v___x_756_);
lean_inc_ref(v___x_753_);
v___x_758_ = l_Lean_Syntax_node3(v_a_748_, v___x_751_, v_b_704_, v___x_753_, v___x_757_);
v___x_759_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3);
v___x_760_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5));
lean_inc(v_currMacroScope_750_);
lean_inc(v_quotContext_749_);
v___x_761_ = l_Lean_addMacroScope(v_quotContext_749_, v___x_760_, v_currMacroScope_750_);
v___x_762_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__10));
v___x_763_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_763_, 0, v_a_748_);
lean_ctor_set(v___x_763_, 1, v___x_759_);
lean_ctor_set(v___x_763_, 2, v___x_761_);
lean_ctor_set(v___x_763_, 3, v___x_762_);
v___x_764_ = l_Lean_Syntax_node3(v_a_748_, v___x_751_, v___x_758_, v___x_753_, v___x_763_);
v___x_765_ = lean_box(0);
lean_inc(v___x_745_);
lean_inc(v___x_702_);
lean_inc(v___x_740_);
v___x_766_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1(v___f_737_, v___x_741_, v___x_739_, v___x_742_, v___x_743_, v___x_740_, v___x_702_, v___x_745_, v___x_765_, v___x_764_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
v___y_713_ = v___x_766_;
goto v___jp_712_;
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
lean_dec(v___x_743_);
lean_dec_ref(v___x_741_);
lean_dec(v_b_704_);
lean_dec(v_a_703_);
lean_dec(v___x_702_);
v_a_767_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_747_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_747_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_772_; 
if (v_isShared_770_ == 0)
{
v___x_772_ = v___x_769_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
else
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = lean_box(0);
lean_inc(v___x_745_);
lean_inc(v___x_702_);
lean_inc(v___x_740_);
v___x_776_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1(v___f_737_, v___x_741_, v___x_739_, v___x_742_, v___x_743_, v___x_740_, v___x_702_, v___x_745_, v___x_775_, v_b_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
v___y_713_ = v___x_776_;
goto v___jp_712_;
}
}
v___jp_712_:
{
if (lean_obj_tag(v___y_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_726_; 
v_a_714_ = lean_ctor_get(v___y_713_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___y_713_);
if (v_isSharedCheck_726_ == 0)
{
v___x_716_ = v___y_713_;
v_isShared_717_ = v_isSharedCheck_726_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___y_713_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_726_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
if (lean_obj_tag(v_a_714_) == 0)
{
lean_object* v_a_718_; lean_object* v___x_720_; 
lean_dec(v_a_703_);
lean_dec(v___x_702_);
v_a_718_ = lean_ctor_get(v_a_714_, 0);
lean_inc(v_a_718_);
lean_dec_ref_known(v_a_714_, 1);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v_a_718_);
v___x_720_ = v___x_716_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_718_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
else
{
lean_object* v_a_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
lean_del_object(v___x_716_);
v_a_722_ = lean_ctor_get(v_a_714_, 0);
lean_inc(v_a_722_);
lean_dec_ref_known(v_a_714_, 1);
v___x_723_ = lean_unsigned_to_nat(1u);
v___x_724_ = lean_nat_add(v_a_703_, v___x_723_);
lean_dec(v_a_703_);
v_a_703_ = v___x_724_;
v_b_704_ = v_a_722_;
goto _start;
}
}
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
lean_dec(v_a_703_);
lean_dec(v___x_702_);
v_a_727_ = lean_ctor_get(v___y_713_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___y_713_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___y_713_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___y_713_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___boxed(lean_object* v_upperBound_777_, lean_object* v___x_778_, lean_object* v___x_779_, lean_object* v_xs_780_, lean_object* v___x_781_, lean_object* v_a_782_, lean_object* v_b_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg(v_upperBound_777_, v___x_778_, v___x_779_, v_xs_780_, v___x_781_, v_a_782_, v_b_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec_ref(v_xs_780_);
lean_dec(v___x_779_);
lean_dec_ref(v___x_778_);
lean_dec(v_upperBound_777_);
return v_res_791_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__1(void){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__0));
v___x_794_ = l_String_toRawSubstring_x27(v___x_793_);
return v___x_794_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__10(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__9));
v___x_816_ = l_String_toRawSubstring_x27(v___x_815_);
return v___x_816_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__19(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__18));
v___x_835_ = l_Lean_stringToMessageData(v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0(lean_object* v___x_836_, lean_object* v_numParams_837_, lean_object* v___x_838_, lean_object* v___x_839_, lean_object* v_xs_840_, lean_object* v_x_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v_ref_849_; lean_object* v_quotContext_850_; lean_object* v_currMacroScope_851_; uint8_t v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; uint8_t v___x_899_; 
v_ref_849_ = lean_ctor_get(v___y_846_, 5);
v_quotContext_850_ = lean_ctor_get(v___y_846_, 10);
v_currMacroScope_851_ = lean_ctor_get(v___y_846_, 11);
v___x_852_ = 0;
v___x_853_ = l_Lean_SourceInfo_fromRef(v_ref_849_, v___x_852_);
v___x_854_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__1, &l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__1_once, _init_l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__1);
v___x_855_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__3));
lean_inc(v_currMacroScope_851_);
lean_inc(v_quotContext_850_);
v___x_856_ = l_Lean_addMacroScope(v_quotContext_850_, v___x_855_, v_currMacroScope_851_);
v___x_857_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__8));
v___x_858_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_858_, 0, v___x_853_);
lean_ctor_set(v___x_858_, 1, v___x_854_);
lean_ctor_set(v___x_858_, 2, v___x_856_);
lean_ctor_set(v___x_858_, 3, v___x_857_);
v___x_896_ = lean_array_get_size(v_xs_840_);
v___x_897_ = lean_array_get_size(v___x_836_);
v___x_898_ = lean_nat_add(v_numParams_837_, v___x_897_);
v___x_899_ = lean_nat_dec_eq(v___x_896_, v___x_898_);
lean_dec(v___x_898_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec_ref_known(v___x_858_, 4);
lean_dec(v___x_839_);
lean_dec(v___x_838_);
v___x_900_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__19, &l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__19_once, _init_l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__19);
v___x_901_ = l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg(v___x_900_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
v_a_902_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_901_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_901_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
else
{
v___y_860_ = v___y_842_;
v___y_861_ = v___y_843_;
v___y_862_ = v___y_844_;
v___y_863_ = v___y_845_;
v___y_864_ = v___y_846_;
v___y_865_ = v___y_847_;
goto v___jp_859_;
}
v___jp_859_:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = lean_array_get_size(v___x_836_);
v___x_867_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg(v___x_866_, v___x_836_, v_numParams_837_, v_xs_840_, v___x_838_, v___x_839_, v___x_858_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_895_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_895_ == 0)
{
v___x_870_ = v___x_867_;
v_isShared_871_ = v_isSharedCheck_895_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_867_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_895_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v_ref_872_; lean_object* v_quotContext_873_; lean_object* v_currMacroScope_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_893_; 
v_ref_872_ = lean_ctor_get(v___y_864_, 5);
v_quotContext_873_ = lean_ctor_get(v___y_864_, 10);
v_currMacroScope_874_ = lean_ctor_get(v___y_864_, 11);
v___x_875_ = l_Lean_SourceInfo_fromRef(v_ref_872_, v___x_852_);
v___x_876_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33));
v___x_877_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__10, &l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__10_once, _init_l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__10);
v___x_878_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__12));
lean_inc(v_currMacroScope_874_);
lean_inc(v_quotContext_873_);
v___x_879_ = l_Lean_addMacroScope(v_quotContext_873_, v___x_878_, v_currMacroScope_874_);
v___x_880_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__15));
lean_inc_n(v___x_875_, 6);
v___x_881_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_881_, 0, v___x_875_);
lean_ctor_set(v___x_881_, 1, v___x_877_);
lean_ctor_set(v___x_881_, 2, v___x_879_);
lean_ctor_set(v___x_881_, 3, v___x_880_);
v___x_882_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_883_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__6));
v___x_884_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__16));
v___x_885_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_875_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
v___x_886_ = l_Lean_Syntax_node1(v___x_875_, v___x_883_, v___x_885_);
v___x_887_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___closed__17));
v___x_888_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_875_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = l_Lean_Syntax_node1(v___x_875_, v___x_883_, v___x_888_);
v___x_890_ = l_Lean_Syntax_node3(v___x_875_, v___x_882_, v___x_886_, v_a_868_, v___x_889_);
v___x_891_ = l_Lean_Syntax_node2(v___x_875_, v___x_876_, v___x_881_, v___x_890_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v___x_891_);
v___x_893_ = v___x_870_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_891_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
else
{
return v___x_867_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___boxed(lean_object* v___x_910_, lean_object* v_numParams_911_, lean_object* v___x_912_, lean_object* v___x_913_, lean_object* v_xs_914_, lean_object* v_x_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0(v___x_910_, v_numParams_911_, v___x_912_, v___x_913_, v_xs_914_, v_x_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec_ref(v_x_915_);
lean_dec_ref(v_xs_914_);
lean_dec(v_numParams_911_);
lean_dec_ref(v___x_910_);
return v_res_923_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_instMonadEIO(lean_box(0));
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0(lean_object* v_msg_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v_toApplicative_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_1032_; 
v___x_939_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__0);
v___x_940_ = l_StateRefT_x27_instMonad___redArg(v___x_939_);
v_toApplicative_941_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_1032_ == 0)
{
lean_object* v_unused_1033_; 
v_unused_1033_ = lean_ctor_get(v___x_940_, 1);
lean_dec(v_unused_1033_);
v___x_943_ = v___x_940_;
v_isShared_944_ = v_isSharedCheck_1032_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_toApplicative_941_);
lean_dec(v___x_940_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_1032_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v_toFunctor_945_; lean_object* v_toSeq_946_; lean_object* v_toSeqLeft_947_; lean_object* v_toSeqRight_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_1030_; 
v_toFunctor_945_ = lean_ctor_get(v_toApplicative_941_, 0);
v_toSeq_946_ = lean_ctor_get(v_toApplicative_941_, 2);
v_toSeqLeft_947_ = lean_ctor_get(v_toApplicative_941_, 3);
v_toSeqRight_948_ = lean_ctor_get(v_toApplicative_941_, 4);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_toApplicative_941_);
if (v_isSharedCheck_1030_ == 0)
{
lean_object* v_unused_1031_; 
v_unused_1031_ = lean_ctor_get(v_toApplicative_941_, 1);
lean_dec(v_unused_1031_);
v___x_950_ = v_toApplicative_941_;
v_isShared_951_ = v_isSharedCheck_1030_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_toSeqRight_948_);
lean_inc(v_toSeqLeft_947_);
lean_inc(v_toSeq_946_);
lean_inc(v_toFunctor_945_);
lean_dec(v_toApplicative_941_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_1030_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___f_952_; lean_object* v___f_953_; lean_object* v___f_954_; lean_object* v___f_955_; lean_object* v___x_956_; lean_object* v___f_957_; lean_object* v___f_958_; lean_object* v___f_959_; lean_object* v___x_961_; 
v___f_952_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__1));
v___f_953_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_945_);
v___f_954_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_954_, 0, v_toFunctor_945_);
v___f_955_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_955_, 0, v_toFunctor_945_);
v___x_956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_956_, 0, v___f_954_);
lean_ctor_set(v___x_956_, 1, v___f_955_);
v___f_957_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_957_, 0, v_toSeqRight_948_);
v___f_958_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_958_, 0, v_toSeqLeft_947_);
v___f_959_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_959_, 0, v_toSeq_946_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 4, v___f_957_);
lean_ctor_set(v___x_950_, 3, v___f_958_);
lean_ctor_set(v___x_950_, 2, v___f_959_);
lean_ctor_set(v___x_950_, 1, v___f_952_);
lean_ctor_set(v___x_950_, 0, v___x_956_);
v___x_961_ = v___x_950_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_956_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v___f_952_);
lean_ctor_set(v_reuseFailAlloc_1029_, 2, v___f_959_);
lean_ctor_set(v_reuseFailAlloc_1029_, 3, v___f_958_);
lean_ctor_set(v_reuseFailAlloc_1029_, 4, v___f_957_);
v___x_961_ = v_reuseFailAlloc_1029_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
lean_object* v___x_963_; 
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 1, v___f_953_);
lean_ctor_set(v___x_943_, 0, v___x_961_);
v___x_963_ = v___x_943_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_961_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v___f_953_);
v___x_963_ = v_reuseFailAlloc_1028_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
lean_object* v___x_964_; lean_object* v_toApplicative_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_1026_; 
v___x_964_ = l_StateRefT_x27_instMonad___redArg(v___x_963_);
v_toApplicative_965_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_1026_ == 0)
{
lean_object* v_unused_1027_; 
v_unused_1027_ = lean_ctor_get(v___x_964_, 1);
lean_dec(v_unused_1027_);
v___x_967_ = v___x_964_;
v_isShared_968_ = v_isSharedCheck_1026_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_toApplicative_965_);
lean_dec(v___x_964_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_1026_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v_toFunctor_969_; lean_object* v_toSeq_970_; lean_object* v_toSeqLeft_971_; lean_object* v_toSeqRight_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_1024_; 
v_toFunctor_969_ = lean_ctor_get(v_toApplicative_965_, 0);
v_toSeq_970_ = lean_ctor_get(v_toApplicative_965_, 2);
v_toSeqLeft_971_ = lean_ctor_get(v_toApplicative_965_, 3);
v_toSeqRight_972_ = lean_ctor_get(v_toApplicative_965_, 4);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_toApplicative_965_);
if (v_isSharedCheck_1024_ == 0)
{
lean_object* v_unused_1025_; 
v_unused_1025_ = lean_ctor_get(v_toApplicative_965_, 1);
lean_dec(v_unused_1025_);
v___x_974_ = v_toApplicative_965_;
v_isShared_975_ = v_isSharedCheck_1024_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_toSeqRight_972_);
lean_inc(v_toSeqLeft_971_);
lean_inc(v_toSeq_970_);
lean_inc(v_toFunctor_969_);
lean_dec(v_toApplicative_965_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_1024_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___f_976_; lean_object* v___f_977_; lean_object* v___f_978_; lean_object* v___f_979_; lean_object* v___x_980_; lean_object* v___f_981_; lean_object* v___f_982_; lean_object* v___f_983_; lean_object* v___x_985_; 
v___f_976_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__3));
v___f_977_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__4));
lean_inc_ref(v_toFunctor_969_);
v___f_978_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_978_, 0, v_toFunctor_969_);
v___f_979_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_979_, 0, v_toFunctor_969_);
v___x_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_980_, 0, v___f_978_);
lean_ctor_set(v___x_980_, 1, v___f_979_);
v___f_981_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_981_, 0, v_toSeqRight_972_);
v___f_982_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_982_, 0, v_toSeqLeft_971_);
v___f_983_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_983_, 0, v_toSeq_970_);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 4, v___f_981_);
lean_ctor_set(v___x_974_, 3, v___f_982_);
lean_ctor_set(v___x_974_, 2, v___f_983_);
lean_ctor_set(v___x_974_, 1, v___f_976_);
lean_ctor_set(v___x_974_, 0, v___x_980_);
v___x_985_ = v___x_974_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_980_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v___f_976_);
lean_ctor_set(v_reuseFailAlloc_1023_, 2, v___f_983_);
lean_ctor_set(v_reuseFailAlloc_1023_, 3, v___f_982_);
lean_ctor_set(v_reuseFailAlloc_1023_, 4, v___f_981_);
v___x_985_ = v_reuseFailAlloc_1023_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
lean_object* v___x_987_; 
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 1, v___f_977_);
lean_ctor_set(v___x_967_, 0, v___x_985_);
v___x_987_ = v___x_967_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v___f_977_);
v___x_987_ = v_reuseFailAlloc_1022_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
lean_object* v___x_988_; lean_object* v_toApplicative_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1020_; 
v___x_988_ = l_StateRefT_x27_instMonad___redArg(v___x_987_);
v_toApplicative_989_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1020_ == 0)
{
lean_object* v_unused_1021_; 
v_unused_1021_ = lean_ctor_get(v___x_988_, 1);
lean_dec(v_unused_1021_);
v___x_991_ = v___x_988_;
v_isShared_992_ = v_isSharedCheck_1020_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_toApplicative_989_);
lean_dec(v___x_988_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1020_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v_toFunctor_993_; lean_object* v_toSeq_994_; lean_object* v_toSeqLeft_995_; lean_object* v_toSeqRight_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1018_; 
v_toFunctor_993_ = lean_ctor_get(v_toApplicative_989_, 0);
v_toSeq_994_ = lean_ctor_get(v_toApplicative_989_, 2);
v_toSeqLeft_995_ = lean_ctor_get(v_toApplicative_989_, 3);
v_toSeqRight_996_ = lean_ctor_get(v_toApplicative_989_, 4);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_toApplicative_989_);
if (v_isSharedCheck_1018_ == 0)
{
lean_object* v_unused_1019_; 
v_unused_1019_ = lean_ctor_get(v_toApplicative_989_, 1);
lean_dec(v_unused_1019_);
v___x_998_ = v_toApplicative_989_;
v_isShared_999_ = v_isSharedCheck_1018_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_toSeqRight_996_);
lean_inc(v_toSeqLeft_995_);
lean_inc(v_toSeq_994_);
lean_inc(v_toFunctor_993_);
lean_dec(v_toApplicative_989_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1018_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___f_1000_; lean_object* v___f_1001_; lean_object* v___f_1002_; lean_object* v___f_1003_; lean_object* v___x_1004_; lean_object* v___f_1005_; lean_object* v___f_1006_; lean_object* v___f_1007_; lean_object* v___x_1009_; 
v___f_1000_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__5));
v___f_1001_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___closed__6));
lean_inc_ref(v_toFunctor_993_);
v___f_1002_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1002_, 0, v_toFunctor_993_);
v___f_1003_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1003_, 0, v_toFunctor_993_);
v___x_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___f_1002_);
lean_ctor_set(v___x_1004_, 1, v___f_1003_);
v___f_1005_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1005_, 0, v_toSeqRight_996_);
v___f_1006_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1006_, 0, v_toSeqLeft_995_);
v___f_1007_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1007_, 0, v_toSeq_994_);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 4, v___f_1005_);
lean_ctor_set(v___x_998_, 3, v___f_1006_);
lean_ctor_set(v___x_998_, 2, v___f_1007_);
lean_ctor_set(v___x_998_, 1, v___f_1000_);
lean_ctor_set(v___x_998_, 0, v___x_1004_);
v___x_1009_ = v___x_998_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1004_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v___f_1000_);
lean_ctor_set(v_reuseFailAlloc_1017_, 2, v___f_1007_);
lean_ctor_set(v_reuseFailAlloc_1017_, 3, v___f_1006_);
lean_ctor_set(v_reuseFailAlloc_1017_, 4, v___f_1005_);
v___x_1009_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
lean_object* v___x_1011_; 
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 1, v___f_1001_);
lean_ctor_set(v___x_991_, 0, v___x_1009_);
v___x_1011_ = v___x_991_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1009_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v___f_1001_);
v___x_1011_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_19815__overap_1014_; lean_object* v___x_1015_; 
v___x_1012_ = lean_box(0);
v___x_1013_ = l_instInhabitedOfMonad___redArg(v___x_1011_, v___x_1012_);
v___x_19815__overap_1014_ = lean_panic_fn_borrowed(v___x_1013_, v_msg_931_);
lean_dec(v___x_1013_);
lean_inc(v___y_937_);
lean_inc_ref(v___y_936_);
lean_inc(v___y_935_);
lean_inc_ref(v___y_934_);
lean_inc(v___y_933_);
lean_inc_ref(v___y_932_);
v___x_1015_ = lean_apply_7(v___x_19815__overap_1014_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, lean_box(0));
return v___x_1015_;
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
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0___boxed(lean_object* v_msg_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0(v_msg_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
return v_res_1042_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__0));
v___x_1045_ = l_Lean_stringToMessageData(v___x_1044_);
return v___x_1045_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__2));
v___x_1048_ = l_Lean_stringToMessageData(v___x_1047_);
return v___x_1048_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__7(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1052_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__6));
v___x_1053_ = lean_unsigned_to_nat(11u);
v___x_1054_ = lean_unsigned_to_nat(122u);
v___x_1055_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__5));
v___x_1056_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__4));
v___x_1057_ = l_mkPanicMessageWithDecl(v___x_1056_, v___x_1055_, v___x_1054_, v___x_1053_, v___x_1052_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0(lean_object* v_constName_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v___x_1074_; lean_object* v_env_1075_; uint8_t v___x_1076_; lean_object* v___x_1077_; 
v___x_1074_ = lean_st_ref_get(v___y_1064_);
v_env_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc_ref(v_env_1075_);
lean_dec(v___x_1074_);
v___x_1076_ = 0;
lean_inc(v_constName_1058_);
v___x_1077_ = l_Lean_Environment_findAsync_x3f(v_env_1075_, v_constName_1058_, v___x_1076_);
if (lean_obj_tag(v___x_1077_) == 1)
{
lean_object* v_val_1078_; uint8_t v_kind_1079_; 
v_val_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_val_1078_);
lean_dec_ref_known(v___x_1077_, 1);
v_kind_1079_ = lean_ctor_get_uint8(v_val_1078_, sizeof(void*)*3);
if (v_kind_1079_ == 6)
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1078_);
if (lean_obj_tag(v___x_1080_) == 6)
{
lean_object* v_val_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1088_; 
lean_dec(v_constName_1058_);
v_val_1081_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1083_ = v___x_1080_;
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_val_1081_);
lean_dec(v___x_1080_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1088_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1086_; 
if (v_isShared_1084_ == 0)
{
lean_ctor_set_tag(v___x_1083_, 0);
v___x_1086_ = v___x_1083_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_val_1081_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
else
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
lean_dec_ref(v___x_1080_);
v___x_1089_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__7);
v___x_1090_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0_spec__0(v___x_1089_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1099_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1093_ = v___x_1090_;
v_isShared_1094_ = v_isSharedCheck_1099_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1090_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1099_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
if (lean_obj_tag(v_a_1091_) == 0)
{
lean_del_object(v___x_1093_);
goto v___jp_1066_;
}
else
{
lean_object* v_val_1095_; lean_object* v___x_1097_; 
lean_dec(v_constName_1058_);
v_val_1095_ = lean_ctor_get(v_a_1091_, 0);
lean_inc(v_val_1095_);
lean_dec_ref_known(v_a_1091_, 1);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 0, v_val_1095_);
v___x_1097_ = v___x_1093_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_val_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_dec(v_constName_1058_);
v_a_1100_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1090_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1090_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
}
else
{
lean_dec(v_val_1078_);
goto v___jp_1066_;
}
}
else
{
lean_dec(v___x_1077_);
goto v___jp_1066_;
}
v___jp_1066_:
{
lean_object* v___x_1067_; uint8_t v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1067_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__1);
v___x_1068_ = 0;
v___x_1069_ = l_Lean_MessageData_ofConstName(v_constName_1058_, v___x_1068_);
v___x_1070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1067_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___closed__3);
v___x_1072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg(v___x_1072_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
return v___x_1073_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0___boxed(lean_object* v_constName_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0(v_constName_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
lean_dec(v___y_1114_);
lean_dec_ref(v___y_1113_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct(lean_object* v_header_1117_, lean_object* v_indVal_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v_toConstantVal_1126_; lean_object* v_numParams_1127_; lean_object* v_ctors_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v_toConstantVal_1126_ = lean_ctor_get(v_indVal_1118_, 0);
lean_inc_ref(v_toConstantVal_1126_);
v_numParams_1127_ = lean_ctor_get(v_indVal_1118_, 1);
lean_inc(v_numParams_1127_);
v_ctors_1128_ = lean_ctor_get(v_indVal_1118_, 4);
lean_inc(v_ctors_1128_);
lean_dec_ref(v_indVal_1118_);
v___x_1129_ = lean_box(0);
v___x_1130_ = l_List_head_x21___redArg(v___x_1129_, v_ctors_1128_);
lean_dec(v_ctors_1128_);
v___x_1131_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0(v___x_1130_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_object* v_a_1132_; lean_object* v___x_1133_; lean_object* v_toConstantVal_1134_; lean_object* v_env_1135_; lean_object* v_name_1136_; lean_object* v_targetNames_1137_; lean_object* v_type_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___f_1143_; uint8_t v___x_1144_; lean_object* v___x_1145_; 
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc(v_a_1132_);
lean_dec_ref_known(v___x_1131_, 1);
v___x_1133_ = lean_st_ref_get(v_a_1124_);
v_toConstantVal_1134_ = lean_ctor_get(v_a_1132_, 0);
lean_inc_ref(v_toConstantVal_1134_);
lean_dec(v_a_1132_);
v_env_1135_ = lean_ctor_get(v___x_1133_, 0);
lean_inc_ref(v_env_1135_);
lean_dec(v___x_1133_);
v_name_1136_ = lean_ctor_get(v_toConstantVal_1126_, 0);
lean_inc(v_name_1136_);
lean_dec_ref(v_toConstantVal_1126_);
v_targetNames_1137_ = lean_ctor_get(v_header_1117_, 2);
v_type_1138_ = lean_ctor_get(v_toConstantVal_1134_, 2);
lean_inc_ref(v_type_1138_);
lean_dec_ref(v_toConstantVal_1134_);
v___x_1139_ = l_Lean_getStructureFields(v_env_1135_, v_name_1136_);
v___x_1140_ = lean_unsigned_to_nat(0u);
v___x_1141_ = lean_array_get_borrowed(v___x_1129_, v_targetNames_1137_, v___x_1140_);
lean_inc(v___x_1141_);
v___x_1142_ = lean_mk_syntax_ident(v___x_1141_);
v___f_1143_ = lean_alloc_closure((void*)(l_Lean_Elab_Deriving_Repr_mkBodyForStruct___lam__0___boxed), 13, 4);
lean_closure_set(v___f_1143_, 0, v___x_1139_);
lean_closure_set(v___f_1143_, 1, v_numParams_1127_);
lean_closure_set(v___f_1143_, 2, v___x_1142_);
lean_closure_set(v___f_1143_, 3, v___x_1140_);
v___x_1144_ = 0;
v___x_1145_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg(v_type_1138_, v___f_1143_, v___x_1144_, v___x_1144_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_);
return v___x_1145_;
}
else
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
lean_dec(v_numParams_1127_);
lean_dec_ref(v_toConstantVal_1126_);
v_a_1146_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1148_ = v___x_1131_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1131_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1146_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForStruct___boxed(lean_object* v_header_1154_, lean_object* v_indVal_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lean_Elab_Deriving_Repr_mkBodyForStruct(v_header_1154_, v_indVal_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_);
lean_dec(v_a_1161_);
lean_dec_ref(v_a_1160_);
lean_dec(v_a_1159_);
lean_dec_ref(v_a_1158_);
lean_dec(v_a_1157_);
lean_dec_ref(v_a_1156_);
lean_dec_ref(v_header_1154_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1(lean_object* v___x_1164_, lean_object* v___x_1165_, lean_object* v_inst_1166_, lean_object* v_R_1167_, lean_object* v_a_1168_, lean_object* v_b_1169_, lean_object* v_c_1170_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___redArg(v___x_1164_, v___x_1165_, v_a_1168_, v_b_1169_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1___boxed(lean_object* v___x_1172_, lean_object* v___x_1173_, lean_object* v_inst_1174_, lean_object* v_R_1175_, lean_object* v_a_1176_, lean_object* v_b_1177_, lean_object* v_c_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__1(v___x_1172_, v___x_1173_, v_inst_1174_, v_R_1175_, v_a_1176_, v_b_1177_, v_c_1178_);
lean_dec_ref(v___x_1173_);
lean_dec_ref(v___x_1172_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2(lean_object* v_upperBound_1180_, lean_object* v___x_1181_, lean_object* v___x_1182_, lean_object* v_xs_1183_, lean_object* v___x_1184_, lean_object* v_inst_1185_, lean_object* v_R_1186_, lean_object* v_a_1187_, lean_object* v_b_1188_, lean_object* v_c_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg(v_upperBound_1180_, v___x_1181_, v___x_1182_, v_xs_1183_, v___x_1184_, v_a_1187_, v_b_1188_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___boxed(lean_object** _args){
lean_object* v_upperBound_1198_ = _args[0];
lean_object* v___x_1199_ = _args[1];
lean_object* v___x_1200_ = _args[2];
lean_object* v_xs_1201_ = _args[3];
lean_object* v___x_1202_ = _args[4];
lean_object* v_inst_1203_ = _args[5];
lean_object* v_R_1204_ = _args[6];
lean_object* v_a_1205_ = _args[7];
lean_object* v_b_1206_ = _args[8];
lean_object* v_c_1207_ = _args[9];
lean_object* v___y_1208_ = _args[10];
lean_object* v___y_1209_ = _args[11];
lean_object* v___y_1210_ = _args[12];
lean_object* v___y_1211_ = _args[13];
lean_object* v___y_1212_ = _args[14];
lean_object* v___y_1213_ = _args[15];
lean_object* v___y_1214_ = _args[16];
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2(v_upperBound_1198_, v___x_1199_, v___x_1200_, v_xs_1201_, v___x_1202_, v_inst_1203_, v_R_1204_, v_a_1205_, v_b_1206_, v_c_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec_ref(v_xs_1201_);
lean_dec(v___x_1200_);
lean_dec_ref(v___x_1199_);
lean_dec(v_upperBound_1198_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3(lean_object* v_00_u03b1_1216_, lean_object* v_msg_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___redArg(v_msg_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3___boxed(lean_object* v_00_u03b1_1226_, lean_object* v_msg_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3(v_00_u03b1_1226_, v_msg_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5(lean_object* v_msgData_1236_, lean_object* v_macroStack_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___redArg(v_msgData_1236_, v_macroStack_1237_, v___y_1242_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5___boxed(lean_object* v_msgData_1246_, lean_object* v_macroStack_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__5(v_msgData_1246_, v_macroStack_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg(lean_object* v_upperBound_1263_, lean_object* v_a_1264_, lean_object* v_b_1265_, lean_object* v___y_1266_){
_start:
{
uint8_t v___x_1268_; 
v___x_1268_ = lean_nat_dec_lt(v_a_1264_, v_upperBound_1263_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1269_; 
lean_dec(v_a_1264_);
v___x_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1269_, 0, v_b_1265_);
return v___x_1269_;
}
else
{
lean_object* v_ref_1270_; uint8_t v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v_ref_1270_ = lean_ctor_get(v___y_1266_, 5);
v___x_1271_ = 0;
v___x_1272_ = l_Lean_SourceInfo_fromRef(v_ref_1270_, v___x_1271_);
v___x_1273_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1));
v___x_1274_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__2));
lean_inc(v___x_1272_);
v___x_1275_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1272_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
v___x_1276_ = l_Lean_Syntax_node1(v___x_1272_, v___x_1273_, v___x_1275_);
v___x_1277_ = lean_array_push(v_b_1265_, v___x_1276_);
v___x_1278_ = lean_unsigned_to_nat(1u);
v___x_1279_ = lean_nat_add(v_a_1264_, v___x_1278_);
lean_dec(v_a_1264_);
v_a_1264_ = v___x_1279_;
v_b_1265_ = v___x_1277_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___boxed(lean_object* v_upperBound_1281_, lean_object* v_a_1282_, lean_object* v_b_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg(v_upperBound_1281_, v_a_1282_, v_b_1283_, v___y_1284_);
lean_dec_ref(v___y_1284_);
lean_dec(v_upperBound_1281_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0(size_t v_sz_1287_, size_t v_i_1288_, lean_object* v_bs_1289_){
_start:
{
uint8_t v___x_1290_; 
v___x_1290_ = lean_usize_dec_lt(v_i_1288_, v_sz_1287_);
if (v___x_1290_ == 0)
{
return v_bs_1289_;
}
else
{
lean_object* v_v_1291_; lean_object* v___x_1292_; lean_object* v_bs_x27_1293_; size_t v___x_1294_; size_t v___x_1295_; lean_object* v___x_1296_; 
v_v_1291_ = lean_array_uget(v_bs_1289_, v_i_1288_);
v___x_1292_ = lean_unsigned_to_nat(0u);
v_bs_x27_1293_ = lean_array_uset(v_bs_1289_, v_i_1288_, v___x_1292_);
v___x_1294_ = ((size_t)1ULL);
v___x_1295_ = lean_usize_add(v_i_1288_, v___x_1294_);
v___x_1296_ = lean_array_uset(v_bs_x27_1293_, v_i_1288_, v_v_1291_);
v_i_1288_ = v___x_1295_;
v_bs_1289_ = v___x_1296_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0___boxed(lean_object* v_sz_1298_, lean_object* v_i_1299_, lean_object* v_bs_1300_){
_start:
{
size_t v_sz_boxed_1301_; size_t v_i_boxed_1302_; lean_object* v_res_1303_; 
v_sz_boxed_1301_ = lean_unbox_usize(v_sz_1298_);
lean_dec(v_sz_1298_);
v_i_boxed_1302_ = lean_unbox_usize(v_i_1299_);
lean_dec(v_i_1299_);
v_res_1303_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0(v_sz_boxed_1301_, v_i_boxed_1302_, v_bs_1300_);
return v_res_1303_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__0));
v___x_1306_ = l_String_toRawSubstring_x27(v___x_1305_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1(lean_object* v___x_1319_, lean_object* v_snd_1320_, lean_object* v_toConstantVal_1321_, lean_object* v___f_1322_, lean_object* v___x_1323_, lean_object* v_auxFunName_1324_, lean_object* v_____r_1325_, lean_object* v_ctorArgs_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v___y_1335_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = l_Lean_Expr_fvarId_x21(v___x_1319_);
v___x_1422_ = l_Lean_FVarId_getBinderInfo___redArg(v___x_1421_, v___y_1329_, v___y_1331_, v___y_1332_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1490_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1425_ = v___x_1422_;
v_isShared_1426_ = v_isSharedCheck_1490_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_a_1423_);
lean_dec(v___x_1422_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1490_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
uint8_t v___x_1427_; uint8_t v___x_1428_; 
v___x_1427_ = lean_unbox(v_a_1423_);
lean_dec(v_a_1423_);
v___x_1428_ = l_Lean_BinderInfo_isExplicit(v___x_1427_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1432_; 
lean_dec(v_auxFunName_1324_);
lean_dec(v___x_1323_);
lean_dec_ref(v___f_1322_);
lean_dec_ref(v___x_1319_);
v___x_1429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1429_, 0, v_ctorArgs_1326_);
lean_ctor_set(v___x_1429_, 1, v_snd_1320_);
v___x_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 0, v___x_1430_);
v___x_1432_ = v___x_1425_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1431_;
}
v_reusejp_1431_:
{
return v___x_1432_;
}
}
else
{
lean_object* v___x_1434_; 
lean_del_object(v___x_1425_);
lean_inc(v___y_1332_);
lean_inc_ref(v___y_1331_);
lean_inc(v___y_1330_);
lean_inc_ref(v___y_1329_);
lean_inc_ref(v___x_1319_);
v___x_1434_ = lean_infer_type(v___x_1319_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; lean_object* v_name_1436_; uint8_t v___x_1437_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1435_);
lean_dec_ref_known(v___x_1434_, 1);
v_name_1436_ = lean_ctor_get(v_toConstantVal_1321_, 0);
v___x_1437_ = l_Lean_Expr_isAppOf(v_a_1435_, v_name_1436_);
lean_dec(v_a_1435_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1438_; 
lean_dec(v_auxFunName_1324_);
lean_inc_ref(v___x_1319_);
v___x_1438_ = l_Lean_Meta_isType(v___x_1319_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_a_1439_; uint8_t v___x_1440_; 
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_a_1439_);
v___x_1440_ = lean_unbox(v_a_1439_);
lean_dec(v_a_1439_);
if (v___x_1440_ == 0)
{
lean_object* v___x_1441_; 
lean_dec_ref_known(v___x_1438_, 1);
v___x_1441_ = l_Lean_Meta_isProof(v___x_1319_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
v___y_1335_ = v___x_1441_;
goto v___jp_1334_;
}
else
{
lean_dec_ref(v___x_1319_);
v___y_1335_ = v___x_1438_;
goto v___jp_1334_;
}
}
else
{
lean_dec_ref(v___x_1319_);
v___y_1335_ = v___x_1438_;
goto v___jp_1334_;
}
}
else
{
lean_object* v___x_1442_; 
lean_dec_ref(v___x_1319_);
lean_inc(v___y_1332_);
lean_inc_ref(v___y_1331_);
lean_inc(v___y_1330_);
lean_inc_ref(v___y_1329_);
lean_inc(v___y_1328_);
lean_inc_ref(v___y_1327_);
v___x_1442_ = lean_apply_7(v___f_1322_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, lean_box(0));
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1473_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1445_ = v___x_1442_;
v_isShared_1446_ = v_isSharedCheck_1473_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1442_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1473_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v_quotContext_1447_; lean_object* v_currMacroScope_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1471_; 
v_quotContext_1447_ = lean_ctor_get(v___y_1331_, 10);
v_currMacroScope_1448_ = lean_ctor_get(v___y_1331_, 11);
v___x_1449_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__3));
v___x_1450_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4));
lean_inc_n(v_a_1443_, 7);
v___x_1451_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1451_, 0, v_a_1443_);
lean_ctor_set(v___x_1451_, 1, v___x_1450_);
v___x_1452_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3);
v___x_1453_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5));
lean_inc(v_currMacroScope_1448_);
lean_inc(v_quotContext_1447_);
v___x_1454_ = l_Lean_addMacroScope(v_quotContext_1447_, v___x_1453_, v_currMacroScope_1448_);
v___x_1455_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__10));
v___x_1456_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1456_, 0, v_a_1443_);
lean_ctor_set(v___x_1456_, 1, v___x_1452_);
lean_ctor_set(v___x_1456_, 2, v___x_1454_);
lean_ctor_set(v___x_1456_, 3, v___x_1455_);
lean_inc_ref(v___x_1451_);
v___x_1457_ = l_Lean_Syntax_node3(v_a_1443_, v___x_1449_, v_snd_1320_, v___x_1451_, v___x_1456_);
v___x_1458_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33));
v___x_1459_ = lean_mk_syntax_ident(v_auxFunName_1324_);
v___x_1460_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_1461_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__6));
v___x_1462_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__7));
v___x_1463_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1463_, 0, v_a_1443_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
v___x_1464_ = l_Lean_Syntax_node1(v_a_1443_, v___x_1461_, v___x_1463_);
v___x_1465_ = l_Lean_Syntax_node2(v_a_1443_, v___x_1460_, v___x_1323_, v___x_1464_);
v___x_1466_ = l_Lean_Syntax_node2(v_a_1443_, v___x_1458_, v___x_1459_, v___x_1465_);
v___x_1467_ = l_Lean_Syntax_node3(v_a_1443_, v___x_1449_, v___x_1457_, v___x_1451_, v___x_1466_);
v___x_1468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1468_, 0, v_ctorArgs_1326_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
v___x_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 0, v___x_1469_);
v___x_1471_ = v___x_1445_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1469_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
else
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
lean_dec_ref(v_ctorArgs_1326_);
lean_dec(v_auxFunName_1324_);
lean_dec(v___x_1323_);
lean_dec(v_snd_1320_);
v_a_1474_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1442_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1442_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1474_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
lean_dec_ref(v_ctorArgs_1326_);
lean_dec(v_auxFunName_1324_);
lean_dec(v___x_1323_);
lean_dec_ref(v___f_1322_);
lean_dec(v_snd_1320_);
lean_dec_ref(v___x_1319_);
v_a_1482_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1434_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1434_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
}
}
}
else
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
lean_dec_ref(v_ctorArgs_1326_);
lean_dec(v_auxFunName_1324_);
lean_dec(v___x_1323_);
lean_dec_ref(v___f_1322_);
lean_dec(v_snd_1320_);
lean_dec_ref(v___x_1319_);
v_a_1491_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1493_ = v___x_1422_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1422_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1491_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
v___jp_1334_:
{
if (lean_obj_tag(v___y_1335_) == 0)
{
lean_object* v_a_1336_; uint8_t v___x_1337_; 
v_a_1336_ = lean_ctor_get(v___y_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref_known(v___y_1335_, 1);
v___x_1337_ = lean_unbox(v_a_1336_);
lean_dec(v_a_1336_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; 
lean_inc(v___y_1332_);
lean_inc_ref(v___y_1331_);
lean_inc(v___y_1330_);
lean_inc_ref(v___y_1329_);
lean_inc(v___y_1328_);
lean_inc_ref(v___y_1327_);
v___x_1338_ = lean_apply_7(v___f_1322_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, lean_box(0));
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1369_; 
v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1341_ = v___x_1338_;
v_isShared_1342_ = v_isSharedCheck_1369_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1338_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1369_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v_quotContext_1343_; lean_object* v_currMacroScope_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1367_; 
v_quotContext_1343_ = lean_ctor_get(v___y_1331_, 10);
v_currMacroScope_1344_ = lean_ctor_get(v___y_1331_, 11);
v___x_1345_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__3));
v___x_1346_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4));
lean_inc_n(v_a_1339_, 6);
v___x_1347_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1347_, 0, v_a_1339_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
v___x_1348_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3);
v___x_1349_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5));
lean_inc_n(v_currMacroScope_1344_, 2);
lean_inc_n(v_quotContext_1343_, 2);
v___x_1350_ = l_Lean_addMacroScope(v_quotContext_1343_, v___x_1349_, v_currMacroScope_1344_);
v___x_1351_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__10));
v___x_1352_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1352_, 0, v_a_1339_);
lean_ctor_set(v___x_1352_, 1, v___x_1348_);
lean_ctor_set(v___x_1352_, 2, v___x_1350_);
lean_ctor_set(v___x_1352_, 3, v___x_1351_);
lean_inc_ref(v___x_1347_);
v___x_1353_ = l_Lean_Syntax_node3(v_a_1339_, v___x_1345_, v_snd_1320_, v___x_1347_, v___x_1352_);
v___x_1354_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33));
v___x_1355_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__1, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__1);
v___x_1356_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__2));
v___x_1357_ = l_Lean_addMacroScope(v_quotContext_1343_, v___x_1356_, v_currMacroScope_1344_);
v___x_1358_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__4));
v___x_1359_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1359_, 0, v_a_1339_);
lean_ctor_set(v___x_1359_, 1, v___x_1355_);
lean_ctor_set(v___x_1359_, 2, v___x_1357_);
lean_ctor_set(v___x_1359_, 3, v___x_1358_);
v___x_1360_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_1361_ = l_Lean_Syntax_node1(v_a_1339_, v___x_1360_, v___x_1323_);
v___x_1362_ = l_Lean_Syntax_node2(v_a_1339_, v___x_1354_, v___x_1359_, v___x_1361_);
v___x_1363_ = l_Lean_Syntax_node3(v_a_1339_, v___x_1345_, v___x_1353_, v___x_1347_, v___x_1362_);
v___x_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1364_, 0, v_ctorArgs_1326_);
lean_ctor_set(v___x_1364_, 1, v___x_1363_);
v___x_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 0, v___x_1365_);
v___x_1367_ = v___x_1341_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec_ref(v_ctorArgs_1326_);
lean_dec(v___x_1323_);
lean_dec(v_snd_1320_);
v_a_1370_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1338_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1338_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
else
{
lean_object* v___x_1378_; 
lean_dec(v___x_1323_);
lean_inc(v___y_1332_);
lean_inc_ref(v___y_1331_);
lean_inc(v___y_1330_);
lean_inc_ref(v___y_1329_);
lean_inc(v___y_1328_);
lean_inc_ref(v___y_1327_);
v___x_1378_ = lean_apply_7(v___f_1322_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, lean_box(0));
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1404_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1381_ = v___x_1378_;
v_isShared_1382_ = v_isSharedCheck_1404_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1378_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1404_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v_quotContext_1383_; lean_object* v_currMacroScope_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1402_; 
v_quotContext_1383_ = lean_ctor_get(v___y_1331_, 10);
v_currMacroScope_1384_ = lean_ctor_get(v___y_1331_, 11);
v___x_1385_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__3));
v___x_1386_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__4));
lean_inc_n(v_a_1379_, 5);
v___x_1387_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1387_, 0, v_a_1379_);
lean_ctor_set(v___x_1387_, 1, v___x_1386_);
v___x_1388_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__3);
v___x_1389_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__5));
lean_inc(v_currMacroScope_1384_);
lean_inc(v_quotContext_1383_);
v___x_1390_ = l_Lean_addMacroScope(v_quotContext_1383_, v___x_1389_, v_currMacroScope_1384_);
v___x_1391_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__10));
v___x_1392_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1392_, 0, v_a_1379_);
lean_ctor_set(v___x_1392_, 1, v___x_1388_);
lean_ctor_set(v___x_1392_, 2, v___x_1390_);
lean_ctor_set(v___x_1392_, 3, v___x_1391_);
lean_inc_ref(v___x_1387_);
v___x_1393_ = l_Lean_Syntax_node3(v_a_1379_, v___x_1385_, v_snd_1320_, v___x_1387_, v___x_1392_);
v___x_1394_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__6));
v___x_1395_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__61));
v___x_1396_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1396_, 0, v_a_1379_);
lean_ctor_set(v___x_1396_, 1, v___x_1395_);
v___x_1397_ = l_Lean_Syntax_node1(v_a_1379_, v___x_1394_, v___x_1396_);
v___x_1398_ = l_Lean_Syntax_node3(v_a_1379_, v___x_1385_, v___x_1393_, v___x_1387_, v___x_1397_);
v___x_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1399_, 0, v_ctorArgs_1326_);
lean_ctor_set(v___x_1399_, 1, v___x_1398_);
v___x_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 0, v___x_1400_);
v___x_1402_ = v___x_1381_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
lean_dec_ref(v_ctorArgs_1326_);
lean_dec(v_snd_1320_);
v_a_1405_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1378_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1378_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
else
{
lean_object* v_a_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1420_; 
lean_dec_ref(v_ctorArgs_1326_);
lean_dec(v___x_1323_);
lean_dec_ref(v___f_1322_);
lean_dec(v_snd_1320_);
v_a_1413_ = lean_ctor_get(v___y_1335_, 0);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___y_1335_);
if (v_isSharedCheck_1420_ == 0)
{
v___x_1415_ = v___y_1335_;
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_a_1413_);
lean_dec(v___y_1335_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1420_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
lean_object* v___x_1418_; 
if (v_isShared_1416_ == 0)
{
v___x_1418_ = v___x_1415_;
goto v_reusejp_1417_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_a_1413_);
v___x_1418_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1417_;
}
v_reusejp_1417_:
{
return v___x_1418_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___boxed(lean_object* v___x_1499_, lean_object* v_snd_1500_, lean_object* v_toConstantVal_1501_, lean_object* v___f_1502_, lean_object* v___x_1503_, lean_object* v_auxFunName_1504_, lean_object* v_____r_1505_, lean_object* v_ctorArgs_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1(v___x_1499_, v_snd_1500_, v_toConstantVal_1501_, v___f_1502_, v___x_1503_, v_auxFunName_1504_, v_____r_1505_, v_ctorArgs_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec_ref(v_toConstantVal_1501_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(lean_object* v_upperBound_1518_, lean_object* v_xs_1519_, lean_object* v_indVal_1520_, lean_object* v_auxFunName_1521_, lean_object* v_header_1522_, lean_object* v_a_1523_, lean_object* v_b_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v___y_1533_; uint8_t v___x_1555_; 
v___x_1555_ = lean_nat_dec_lt(v_a_1523_, v_upperBound_1518_);
if (v___x_1555_ == 0)
{
lean_object* v___x_1556_; 
lean_dec(v_a_1523_);
lean_dec(v_auxFunName_1521_);
v___x_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1556_, 0, v_b_1524_);
return v___x_1556_;
}
else
{
lean_object* v_fst_1557_; lean_object* v_snd_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1606_; 
v_fst_1557_ = lean_ctor_get(v_b_1524_, 0);
v_snd_1558_ = lean_ctor_get(v_b_1524_, 1);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_b_1524_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1560_ = v_b_1524_;
v_isShared_1561_ = v_isSharedCheck_1606_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_snd_1558_);
lean_inc(v_fst_1557_);
lean_dec(v_b_1524_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1606_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v_toConstantVal_1562_; lean_object* v_numParams_1563_; lean_object* v___f_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; lean_object* v_a_1568_; 
v_toConstantVal_1562_ = lean_ctor_get(v_indVal_1520_, 0);
v_numParams_1563_ = lean_ctor_get(v_indVal_1520_, 1);
v___f_1564_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___closed__0));
v___x_1565_ = lean_array_fget_borrowed(v_xs_1519_, v_a_1523_);
v___x_1566_ = lean_nat_dec_lt(v_a_1523_, v_numParams_1563_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___closed__1));
v___x_1593_ = l_Lean_Core_mkFreshUserName(v___x_1592_, v___y_1529_, v___y_1530_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1594_);
lean_dec_ref_known(v___x_1593_, 1);
v_a_1568_ = v_a_1594_;
goto v___jp_1567_;
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
lean_del_object(v___x_1560_);
lean_dec(v_snd_1558_);
lean_dec(v_fst_1557_);
lean_dec(v_a_1523_);
lean_dec(v_auxFunName_1521_);
v_a_1595_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1597_ = v___x_1593_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1593_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_a_1595_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
else
{
lean_object* v_argNames_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v_argNames_1603_ = lean_ctor_get(v_header_1522_, 1);
v___x_1604_ = lean_box(0);
v___x_1605_ = lean_array_get_borrowed(v___x_1604_, v_argNames_1603_, v_a_1523_);
lean_inc(v___x_1605_);
v_a_1568_ = v___x_1605_;
goto v___jp_1567_;
}
v___jp_1567_:
{
lean_object* v___x_1569_; 
v___x_1569_ = lean_mk_syntax_ident(v_a_1568_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
lean_del_object(v___x_1560_);
lean_inc(v___x_1569_);
v___x_1570_ = lean_array_push(v_fst_1557_, v___x_1569_);
v___x_1571_ = lean_box(0);
lean_inc(v_auxFunName_1521_);
lean_inc(v___x_1565_);
v___x_1572_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1(v___x_1565_, v_snd_1558_, v_toConstantVal_1562_, v___f_1564_, v___x_1569_, v_auxFunName_1521_, v___x_1571_, v___x_1570_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
v___y_1533_ = v___x_1572_;
goto v___jp_1532_;
}
else
{
lean_object* v___x_1573_; 
v___x_1573_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__0(v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
if (lean_obj_tag(v___x_1573_) == 0)
{
lean_object* v_a_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1578_; 
v_a_1574_ = lean_ctor_get(v___x_1573_, 0);
lean_inc_n(v_a_1574_, 2);
lean_dec_ref_known(v___x_1573_, 1);
v___x_1575_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__1));
v___x_1576_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg___closed__2));
if (v_isShared_1561_ == 0)
{
lean_ctor_set_tag(v___x_1560_, 2);
lean_ctor_set(v___x_1560_, 1, v___x_1576_);
lean_ctor_set(v___x_1560_, 0, v_a_1574_);
v___x_1578_ = v___x_1560_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1574_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1579_ = l_Lean_Syntax_node1(v_a_1574_, v___x_1575_, v___x_1578_);
v___x_1580_ = lean_array_push(v_fst_1557_, v___x_1579_);
v___x_1581_ = lean_box(0);
lean_inc(v_auxFunName_1521_);
lean_inc(v___x_1565_);
v___x_1582_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1(v___x_1565_, v_snd_1558_, v_toConstantVal_1562_, v___f_1564_, v___x_1569_, v_auxFunName_1521_, v___x_1581_, v___x_1580_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
v___y_1533_ = v___x_1582_;
goto v___jp_1532_;
}
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
lean_dec(v___x_1569_);
lean_del_object(v___x_1560_);
lean_dec(v_snd_1558_);
lean_dec(v_fst_1557_);
lean_dec(v_a_1523_);
lean_dec(v_auxFunName_1521_);
v_a_1584_ = lean_ctor_get(v___x_1573_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1573_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1573_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
}
}
}
v___jp_1532_:
{
if (lean_obj_tag(v___y_1533_) == 0)
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1546_; 
v_a_1534_ = lean_ctor_get(v___y_1533_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___y_1533_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1536_ = v___y_1533_;
v_isShared_1537_ = v_isSharedCheck_1546_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___y_1533_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1546_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
if (lean_obj_tag(v_a_1534_) == 0)
{
lean_object* v_a_1538_; lean_object* v___x_1540_; 
lean_dec(v_a_1523_);
lean_dec(v_auxFunName_1521_);
v_a_1538_ = lean_ctor_get(v_a_1534_, 0);
lean_inc(v_a_1538_);
lean_dec_ref_known(v_a_1534_, 1);
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 0, v_a_1538_);
v___x_1540_ = v___x_1536_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1538_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
else
{
lean_object* v_a_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
lean_del_object(v___x_1536_);
v_a_1542_ = lean_ctor_get(v_a_1534_, 0);
lean_inc(v_a_1542_);
lean_dec_ref_known(v_a_1534_, 1);
v___x_1543_ = lean_unsigned_to_nat(1u);
v___x_1544_ = lean_nat_add(v_a_1523_, v___x_1543_);
lean_dec(v_a_1523_);
v_a_1523_ = v___x_1544_;
v_b_1524_ = v_a_1542_;
goto _start;
}
}
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
lean_dec(v_a_1523_);
lean_dec(v_auxFunName_1521_);
v_a_1547_ = lean_ctor_get(v___y_1533_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___y_1533_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___y_1533_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___y_1533_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___boxed(lean_object* v_upperBound_1607_, lean_object* v_xs_1608_, lean_object* v_indVal_1609_, lean_object* v_auxFunName_1610_, lean_object* v_header_1611_, lean_object* v_a_1612_, lean_object* v_b_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(v_upperBound_1607_, v_xs_1608_, v_indVal_1609_, v_auxFunName_1610_, v_header_1611_, v_a_1612_, v_b_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec_ref(v_header_1611_);
lean_dec_ref(v_indVal_1609_);
lean_dec_ref(v_xs_1608_);
lean_dec(v_upperBound_1607_);
return v_res_1621_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__4));
v___x_1635_ = l_String_toRawSubstring_x27(v___x_1634_);
return v___x_1635_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16(void){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1659_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__15));
v___x_1660_ = l_Lean_mkAtom(v___x_1659_);
return v___x_1660_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__19(void){
_start:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1663_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__18));
v___x_1664_ = l_String_toRawSubstring_x27(v___x_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1(lean_object* v_indVal_1720_, lean_object* v___x_1721_, lean_object* v_alts_1722_, lean_object* v_name_1723_, lean_object* v_auxFunName_1724_, lean_object* v_header_1725_, lean_object* v___f_1726_, lean_object* v_head_1727_, lean_object* v_xs_1728_, lean_object* v_x_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v_numIndices_1737_; lean_object* v___x_1738_; 
v_numIndices_1737_ = lean_ctor_get(v_indVal_1720_, 2);
lean_inc_ref(v_alts_1722_);
lean_inc(v___x_1721_);
v___x_1738_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg(v_numIndices_1737_, v___x_1721_, v_alts_1722_, v___y_1734_);
if (lean_obj_tag(v___x_1738_) == 0)
{
lean_object* v_a_1739_; lean_object* v_ref_1740_; lean_object* v_quotContext_1741_; lean_object* v_currMacroScope_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; uint8_t v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; uint8_t v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_a_1739_);
lean_dec_ref_known(v___x_1738_, 1);
v_ref_1740_ = lean_ctor_get(v___y_1734_, 5);
v_quotContext_1741_ = lean_ctor_get(v___y_1734_, 10);
v_currMacroScope_1742_ = lean_ctor_get(v___y_1734_, 11);
v___x_1743_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__1));
v___x_1744_ = lean_box(0);
v___x_1745_ = lean_array_get_size(v_xs_1728_);
v___x_1746_ = 0;
v___x_1747_ = l_Lean_SourceInfo_fromRef(v_ref_1740_, v___x_1746_);
v___x_1748_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__5);
lean_inc(v_currMacroScope_1742_);
lean_inc(v_quotContext_1741_);
v___x_1749_ = l_Lean_addMacroScope(v_quotContext_1741_, v___x_1743_, v_currMacroScope_1742_);
v___x_1750_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__8));
lean_inc_n(v___x_1747_, 2);
v___x_1751_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1747_);
lean_ctor_set(v___x_1751_, 1, v___x_1748_);
lean_ctor_set(v___x_1751_, 2, v___x_1749_);
lean_ctor_set(v___x_1751_, 3, v___x_1750_);
v___x_1752_ = 1;
v___x_1753_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1723_, v___x_1752_);
v___x_1754_ = lean_box(2);
v___x_1755_ = l_Lean_Syntax_mkStrLit(v___x_1753_, v___x_1754_);
v___x_1756_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_1757_ = l_Lean_Syntax_node1(v___x_1747_, v___x_1756_, v___x_1755_);
v___x_1758_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__33));
v___x_1759_ = l_Lean_Syntax_node2(v___x_1747_, v___x_1758_, v___x_1751_, v___x_1757_);
v___x_1760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1760_, 0, v_alts_1722_);
lean_ctor_set(v___x_1760_, 1, v___x_1759_);
v___x_1761_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(v___x_1745_, v_xs_1728_, v_indVal_1720_, v_auxFunName_1724_, v_header_1725_, v___x_1721_, v___x_1760_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1763_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref_known(v___x_1761_, 1);
lean_inc_ref(v___f_1726_);
lean_inc(v___y_1735_);
lean_inc_ref(v___y_1734_);
lean_inc(v___y_1733_);
lean_inc_ref(v___y_1732_);
lean_inc(v___y_1731_);
lean_inc_ref(v___y_1730_);
v___x_1763_ = lean_apply_7(v___f_1726_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, lean_box(0));
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1765_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref_known(v___x_1763_, 1);
lean_inc(v___y_1735_);
lean_inc_ref(v___y_1734_);
lean_inc(v___y_1733_);
lean_inc_ref(v___y_1732_);
lean_inc(v___y_1731_);
lean_inc_ref(v___y_1730_);
v___x_1765_ = lean_apply_7(v___f_1726_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, lean_box(0));
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1871_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1768_ = v___x_1765_;
v_isShared_1769_ = v_isSharedCheck_1871_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1765_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1871_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v_fst_1770_; lean_object* v_snd_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1870_; 
v_fst_1770_ = lean_ctor_get(v_a_1762_, 0);
v_snd_1771_ = lean_ctor_get(v_a_1762_, 1);
v_isSharedCheck_1870_ = !lean_is_exclusive(v_a_1762_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1773_ = v_a_1762_;
v_isShared_1774_ = v_isSharedCheck_1870_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_snd_1771_);
lean_inc(v_fst_1770_);
lean_dec(v_a_1762_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1870_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1775_; lean_object* v___x_1777_; 
v___x_1775_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__9));
lean_inc(v_a_1764_);
if (v_isShared_1774_ == 0)
{
lean_ctor_set_tag(v___x_1773_, 2);
lean_ctor_set(v___x_1773_, 1, v___x_1775_);
lean_ctor_set(v___x_1773_, 0, v_a_1764_);
v___x_1777_ = v___x_1773_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1764_);
lean_ctor_set(v_reuseFailAlloc_1869_, 1, v___x_1775_);
v___x_1777_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; size_t v_sz_1789_; size_t v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1867_; 
v___x_1778_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__11));
v___x_1779_ = lean_mk_syntax_ident(v_head_1727_);
lean_inc_n(v_a_1764_, 2);
v___x_1780_ = l_Lean_Syntax_node2(v_a_1764_, v___x_1778_, v___x_1777_, v___x_1779_);
v___x_1781_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22);
v___x_1782_ = l_Array_append___redArg(v___x_1781_, v_fst_1770_);
lean_dec(v_fst_1770_);
v___x_1783_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1783_, 0, v_a_1764_);
lean_ctor_set(v___x_1783_, 1, v___x_1756_);
lean_ctor_set(v___x_1783_, 2, v___x_1782_);
v___x_1784_ = l_Lean_Syntax_node2(v_a_1764_, v___x_1758_, v___x_1780_, v___x_1783_);
v___x_1785_ = lean_array_push(v_a_1739_, v___x_1784_);
v___x_1786_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__13));
v___x_1787_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__14));
lean_inc_n(v_a_1766_, 35);
v___x_1788_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1788_, 0, v_a_1766_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
v_sz_1789_ = lean_array_size(v___x_1785_);
v___x_1790_ = ((size_t)0ULL);
v___x_1791_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0(v_sz_1789_, v___x_1790_, v___x_1785_);
v___x_1792_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16);
v___x_1793_ = l_Lean_mkSepArray(v___x_1791_, v___x_1792_);
lean_dec_ref(v___x_1791_);
v___x_1794_ = l_Array_append___redArg(v___x_1781_, v___x_1793_);
lean_dec_ref(v___x_1793_);
v___x_1795_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1795_, 0, v_a_1766_);
lean_ctor_set(v___x_1795_, 1, v___x_1756_);
lean_ctor_set(v___x_1795_, 2, v___x_1794_);
v___x_1796_ = l_Lean_Syntax_node1(v_a_1766_, v___x_1756_, v___x_1795_);
v___x_1797_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__17));
v___x_1798_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1798_, 0, v_a_1766_);
lean_ctor_set(v___x_1798_, 1, v___x_1797_);
v___x_1799_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__19, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__19_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__19);
v___x_1800_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__21));
lean_inc_n(v_currMacroScope_1742_, 5);
lean_inc_n(v_quotContext_1741_, 5);
v___x_1801_ = l_Lean_addMacroScope(v_quotContext_1741_, v___x_1800_, v_currMacroScope_1742_);
v___x_1802_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__23));
v___x_1803_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1803_, 0, v_a_1766_);
lean_ctor_set(v___x_1803_, 1, v___x_1799_);
lean_ctor_set(v___x_1803_, 2, v___x_1801_);
lean_ctor_set(v___x_1803_, 3, v___x_1802_);
v___x_1804_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__9));
v___x_1805_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__11));
v___x_1806_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__7));
v___x_1807_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1807_, 0, v_a_1766_);
lean_ctor_set(v___x_1807_, 1, v___x_1806_);
v___x_1808_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__13));
v___x_1809_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__15);
v___x_1810_ = lean_box(0);
v___x_1811_ = l_Lean_addMacroScope(v_quotContext_1741_, v___x_1810_, v_currMacroScope_1742_);
v___x_1812_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__27));
v___x_1813_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1813_, 0, v_a_1766_);
lean_ctor_set(v___x_1813_, 1, v___x_1809_);
lean_ctor_set(v___x_1813_, 2, v___x_1811_);
lean_ctor_set(v___x_1813_, 3, v___x_1812_);
v___x_1814_ = l_Lean_Syntax_node1(v_a_1766_, v___x_1808_, v___x_1813_);
v___x_1815_ = l_Lean_Syntax_node2(v_a_1766_, v___x_1805_, v___x_1807_, v___x_1814_);
v___x_1816_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__35);
v___x_1817_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__38));
v___x_1818_ = l_Lean_addMacroScope(v_quotContext_1741_, v___x_1817_, v_currMacroScope_1742_);
v___x_1819_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__30));
v___x_1820_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1820_, 0, v_a_1766_);
lean_ctor_set(v___x_1820_, 1, v___x_1816_);
lean_ctor_set(v___x_1820_, 2, v___x_1818_);
lean_ctor_set(v___x_1820_, 3, v___x_1819_);
v___x_1821_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__45, &l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__45_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__45);
v___x_1822_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__47));
v___x_1823_ = l_Lean_addMacroScope(v_quotContext_1741_, v___x_1822_, v_currMacroScope_1742_);
v___x_1824_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__33));
v___x_1825_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1825_, 0, v_a_1766_);
lean_ctor_set(v___x_1825_, 1, v___x_1821_);
lean_ctor_set(v___x_1825_, 2, v___x_1823_);
lean_ctor_set(v___x_1825_, 3, v___x_1824_);
v___x_1826_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__35));
v___x_1827_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__36));
v___x_1828_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1828_, 0, v_a_1766_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
v___x_1829_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__38));
v___x_1830_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__11);
v___x_1831_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__12));
v___x_1832_ = l_Lean_addMacroScope(v_quotContext_1741_, v___x_1831_, v_currMacroScope_1742_);
v___x_1833_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1833_, 0, v_a_1766_);
lean_ctor_set(v___x_1833_, 1, v___x_1830_);
lean_ctor_set(v___x_1833_, 2, v___x_1832_);
lean_ctor_set(v___x_1833_, 3, v___x_1744_);
v___x_1834_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__39));
v___x_1835_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1835_, 0, v_a_1766_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
v___x_1836_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__6));
v___x_1837_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg___lam__1___closed__7));
v___x_1838_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1838_, 0, v_a_1766_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v___x_1839_ = l_Lean_Syntax_node1(v_a_1766_, v___x_1836_, v___x_1838_);
lean_inc_ref(v___x_1833_);
v___x_1840_ = l_Lean_Syntax_node3(v_a_1766_, v___x_1829_, v___x_1833_, v___x_1835_, v___x_1839_);
v___x_1841_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__40));
v___x_1842_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1842_, 0, v_a_1766_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
v___x_1843_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__42));
v___x_1844_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__43));
v___x_1845_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1845_, 0, v_a_1766_);
lean_ctor_set(v___x_1845_, 1, v___x_1844_);
v___x_1846_ = l_Lean_Syntax_node1(v_a_1766_, v___x_1843_, v___x_1845_);
v___x_1847_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__44));
v___x_1848_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1848_, 0, v_a_1766_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
v___x_1849_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__45));
v___x_1850_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1850_, 0, v_a_1766_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
v___x_1851_ = l_Lean_Syntax_node1(v_a_1766_, v___x_1843_, v___x_1850_);
v___x_1852_ = l_Lean_Syntax_node6(v_a_1766_, v___x_1826_, v___x_1828_, v___x_1840_, v___x_1842_, v___x_1846_, v___x_1848_, v___x_1851_);
v___x_1853_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__23));
v___x_1854_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1854_, 0, v_a_1766_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
lean_inc_ref_n(v___x_1854_, 3);
lean_inc_n(v___x_1815_, 3);
v___x_1855_ = l_Lean_Syntax_node3(v_a_1766_, v___x_1804_, v___x_1815_, v___x_1852_, v___x_1854_);
v___x_1856_ = l_Lean_Syntax_node3(v_a_1766_, v___x_1804_, v___x_1815_, v_snd_1771_, v___x_1854_);
v___x_1857_ = l_Lean_Syntax_node2(v_a_1766_, v___x_1756_, v___x_1855_, v___x_1856_);
v___x_1858_ = l_Lean_Syntax_node2(v_a_1766_, v___x_1758_, v___x_1825_, v___x_1857_);
v___x_1859_ = l_Lean_Syntax_node3(v_a_1766_, v___x_1804_, v___x_1815_, v___x_1858_, v___x_1854_);
v___x_1860_ = l_Lean_Syntax_node1(v_a_1766_, v___x_1756_, v___x_1859_);
v___x_1861_ = l_Lean_Syntax_node2(v_a_1766_, v___x_1758_, v___x_1820_, v___x_1860_);
v___x_1862_ = l_Lean_Syntax_node3(v_a_1766_, v___x_1804_, v___x_1815_, v___x_1861_, v___x_1854_);
v___x_1863_ = l_Lean_Syntax_node2(v_a_1766_, v___x_1756_, v___x_1862_, v___x_1833_);
v___x_1864_ = l_Lean_Syntax_node2(v_a_1766_, v___x_1758_, v___x_1803_, v___x_1863_);
v___x_1865_ = l_Lean_Syntax_node4(v_a_1766_, v___x_1786_, v___x_1788_, v___x_1796_, v___x_1798_, v___x_1864_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v___x_1865_);
v___x_1867_ = v___x_1768_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
}
}
else
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
lean_dec(v_a_1764_);
lean_dec(v_a_1762_);
lean_dec(v_a_1739_);
lean_dec(v_head_1727_);
v_a_1872_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___x_1765_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1765_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1872_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_dec(v_a_1762_);
lean_dec(v_a_1739_);
lean_dec(v_head_1727_);
lean_dec_ref(v___f_1726_);
v_a_1880_ = lean_ctor_get(v___x_1763_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1763_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1763_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1763_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
else
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_dec(v_a_1739_);
lean_dec(v_head_1727_);
lean_dec_ref(v___f_1726_);
v_a_1888_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1761_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1761_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
else
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1903_; 
lean_dec(v_head_1727_);
lean_dec_ref(v___f_1726_);
lean_dec(v_auxFunName_1724_);
lean_dec(v_name_1723_);
lean_dec_ref(v_alts_1722_);
lean_dec(v___x_1721_);
v_a_1896_ = lean_ctor_get(v___x_1738_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1738_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1898_ = v___x_1738_;
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1738_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1901_; 
if (v_isShared_1899_ == 0)
{
v___x_1901_ = v___x_1898_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1896_);
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
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_indVal_1904_ = _args[0];
lean_object* v___x_1905_ = _args[1];
lean_object* v_alts_1906_ = _args[2];
lean_object* v_name_1907_ = _args[3];
lean_object* v_auxFunName_1908_ = _args[4];
lean_object* v_header_1909_ = _args[5];
lean_object* v___f_1910_ = _args[6];
lean_object* v_head_1911_ = _args[7];
lean_object* v_xs_1912_ = _args[8];
lean_object* v_x_1913_ = _args[9];
lean_object* v___y_1914_ = _args[10];
lean_object* v___y_1915_ = _args[11];
lean_object* v___y_1916_ = _args[12];
lean_object* v___y_1917_ = _args[13];
lean_object* v___y_1918_ = _args[14];
lean_object* v___y_1919_ = _args[15];
lean_object* v___y_1920_ = _args[16];
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1(v_indVal_1904_, v___x_1905_, v_alts_1906_, v_name_1907_, v_auxFunName_1908_, v_header_1909_, v___f_1910_, v_head_1911_, v_xs_1912_, v_x_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec_ref(v_x_1913_);
lean_dec_ref(v_xs_1912_);
lean_dec_ref(v_header_1909_);
lean_dec_ref(v_indVal_1904_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__0(lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v_ref_1929_; uint8_t v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v_ref_1929_ = lean_ctor_get(v___y_1926_, 5);
v___x_1930_ = 0;
v___x_1931_ = l_Lean_SourceInfo_fromRef(v_ref_1929_, v___x_1930_);
v___x_1932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1931_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__0___boxed(lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__0(v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg(lean_object* v_indVal_1944_, lean_object* v_auxFunName_1945_, lean_object* v_header_1946_, lean_object* v_as_x27_1947_, lean_object* v_b_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
if (lean_obj_tag(v_as_x27_1947_) == 0)
{
lean_object* v___x_1956_; 
lean_dec_ref(v_header_1946_);
lean_dec(v_auxFunName_1945_);
lean_dec_ref(v_indVal_1944_);
v___x_1956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1956_, 0, v_b_1948_);
return v___x_1956_;
}
else
{
lean_object* v_head_1957_; lean_object* v_tail_1958_; lean_object* v___x_1959_; 
v_head_1957_ = lean_ctor_get(v_as_x27_1947_, 0);
v_tail_1958_ = lean_ctor_get(v_as_x27_1947_, 1);
lean_inc(v_head_1957_);
v___x_1959_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__0(v_head_1957_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_a_1960_; lean_object* v_toConstantVal_1961_; lean_object* v_name_1962_; lean_object* v_type_1963_; lean_object* v___f_1964_; lean_object* v___x_1965_; lean_object* v_alts_1966_; lean_object* v___f_1967_; uint8_t v___x_1968_; lean_object* v___x_1969_; 
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_a_1960_);
lean_dec_ref_known(v___x_1959_, 1);
v_toConstantVal_1961_ = lean_ctor_get(v_a_1960_, 0);
lean_inc_ref(v_toConstantVal_1961_);
lean_dec(v_a_1960_);
v_name_1962_ = lean_ctor_get(v_toConstantVal_1961_, 0);
lean_inc(v_name_1962_);
v_type_1963_ = lean_ctor_get(v_toConstantVal_1961_, 2);
lean_inc_ref(v_type_1963_);
lean_dec_ref(v_toConstantVal_1961_);
v___f_1964_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__0));
v___x_1965_ = lean_unsigned_to_nat(0u);
v_alts_1966_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__1));
lean_inc(v_head_1957_);
lean_inc_ref(v_header_1946_);
lean_inc(v_auxFunName_1945_);
lean_inc_ref(v_indVal_1944_);
v___f_1967_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___boxed), 17, 8);
lean_closure_set(v___f_1967_, 0, v_indVal_1944_);
lean_closure_set(v___f_1967_, 1, v___x_1965_);
lean_closure_set(v___f_1967_, 2, v_alts_1966_);
lean_closure_set(v___f_1967_, 3, v_name_1962_);
lean_closure_set(v___f_1967_, 4, v_auxFunName_1945_);
lean_closure_set(v___f_1967_, 5, v_header_1946_);
lean_closure_set(v___f_1967_, 6, v___f_1964_);
lean_closure_set(v___f_1967_, 7, v_head_1957_);
v___x_1968_ = 0;
v___x_1969_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__4___redArg(v_type_1963_, v___f_1967_, v___x_1968_, v___x_1968_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; lean_object* v___x_1971_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_a_1970_);
lean_dec_ref_known(v___x_1969_, 1);
v___x_1971_ = lean_array_push(v_b_1948_, v_a_1970_);
v_as_x27_1947_ = v_tail_1958_;
v_b_1948_ = v___x_1971_;
goto _start;
}
else
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
lean_dec_ref(v_b_1948_);
lean_dec_ref(v_header_1946_);
lean_dec(v_auxFunName_1945_);
lean_dec_ref(v_indVal_1944_);
v_a_1973_ = lean_ctor_get(v___x_1969_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1969_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1969_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1969_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
else
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
lean_dec_ref(v_b_1948_);
lean_dec_ref(v_header_1946_);
lean_dec(v_auxFunName_1945_);
lean_dec_ref(v_indVal_1944_);
v_a_1981_ = lean_ctor_get(v___x_1959_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1959_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1959_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___boxed(lean_object* v_indVal_1989_, lean_object* v_auxFunName_1990_, lean_object* v_header_1991_, lean_object* v_as_x27_1992_, lean_object* v_b_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg(v_indVal_1989_, v_auxFunName_1990_, v_header_1991_, v_as_x27_1992_, v_b_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v_as_x27_1992_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4(size_t v_sz_2002_, size_t v_i_2003_, lean_object* v_bs_2004_){
_start:
{
uint8_t v___x_2005_; 
v___x_2005_ = lean_usize_dec_lt(v_i_2003_, v_sz_2002_);
if (v___x_2005_ == 0)
{
return v_bs_2004_;
}
else
{
lean_object* v_v_2006_; lean_object* v___x_2007_; lean_object* v_bs_x27_2008_; size_t v___x_2009_; size_t v___x_2010_; lean_object* v___x_2011_; 
v_v_2006_ = lean_array_uget(v_bs_2004_, v_i_2003_);
v___x_2007_ = lean_unsigned_to_nat(0u);
v_bs_x27_2008_ = lean_array_uset(v_bs_2004_, v_i_2003_, v___x_2007_);
v___x_2009_ = ((size_t)1ULL);
v___x_2010_ = lean_usize_add(v_i_2003_, v___x_2009_);
v___x_2011_ = lean_array_uset(v_bs_x27_2008_, v_i_2003_, v_v_2006_);
v_i_2003_ = v___x_2010_;
v_bs_2004_ = v___x_2011_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4___boxed(lean_object* v_sz_2013_, lean_object* v_i_2014_, lean_object* v_bs_2015_){
_start:
{
size_t v_sz_boxed_2016_; size_t v_i_boxed_2017_; lean_object* v_res_2018_; 
v_sz_boxed_2016_ = lean_unbox_usize(v_sz_2013_);
lean_dec(v_sz_2013_);
v_i_boxed_2017_ = lean_unbox_usize(v_i_2014_);
lean_dec(v_i_2014_);
v_res_2018_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4(v_sz_boxed_2016_, v_i_boxed_2017_, v_bs_2015_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts(lean_object* v_header_2019_, lean_object* v_indVal_2020_, lean_object* v_auxFunName_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_){
_start:
{
lean_object* v_ctors_2029_; lean_object* v_alts_2030_; lean_object* v___x_2031_; 
v_ctors_2029_ = lean_ctor_get(v_indVal_2020_, 4);
lean_inc(v_ctors_2029_);
v_alts_2030_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__1));
v___x_2031_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg(v_indVal_2020_, v_auxFunName_2021_, v_header_2019_, v_ctors_2029_, v_alts_2030_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_, v_a_2027_);
lean_dec(v_ctors_2029_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2042_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2034_ = v___x_2031_;
v_isShared_2035_ = v_isSharedCheck_2042_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2031_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2042_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
size_t v_sz_2036_; size_t v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2040_; 
v_sz_2036_ = lean_array_size(v_a_2032_);
v___x_2037_ = ((size_t)0ULL);
v___x_2038_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__4(v_sz_2036_, v___x_2037_, v_a_2032_);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 0, v___x_2038_);
v___x_2040_ = v___x_2034_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2038_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
else
{
return v___x_2031_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts___boxed(lean_object* v_header_2043_, lean_object* v_indVal_2044_, lean_object* v_auxFunName_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts(v_header_2043_, v_indVal_2044_, v_auxFunName_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
lean_dec(v_a_2051_);
lean_dec_ref(v_a_2050_);
lean_dec(v_a_2049_);
lean_dec_ref(v_a_2048_);
lean_dec(v_a_2047_);
lean_dec_ref(v_a_2046_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1(lean_object* v_upperBound_2054_, lean_object* v_xs_2055_, lean_object* v_indVal_2056_, lean_object* v_auxFunName_2057_, lean_object* v_header_2058_, lean_object* v_inst_2059_, lean_object* v_R_2060_, lean_object* v_a_2061_, lean_object* v_b_2062_, lean_object* v_c_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v___x_2071_; 
v___x_2071_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___redArg(v_upperBound_2054_, v_xs_2055_, v_indVal_2056_, v_auxFunName_2057_, v_header_2058_, v_a_2061_, v_b_2062_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2072_ = _args[0];
lean_object* v_xs_2073_ = _args[1];
lean_object* v_indVal_2074_ = _args[2];
lean_object* v_auxFunName_2075_ = _args[3];
lean_object* v_header_2076_ = _args[4];
lean_object* v_inst_2077_ = _args[5];
lean_object* v_R_2078_ = _args[6];
lean_object* v_a_2079_ = _args[7];
lean_object* v_b_2080_ = _args[8];
lean_object* v_c_2081_ = _args[9];
lean_object* v___y_2082_ = _args[10];
lean_object* v___y_2083_ = _args[11];
lean_object* v___y_2084_ = _args[12];
lean_object* v___y_2085_ = _args[13];
lean_object* v___y_2086_ = _args[14];
lean_object* v___y_2087_ = _args[15];
lean_object* v___y_2088_ = _args[16];
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__1(v_upperBound_2072_, v_xs_2073_, v_indVal_2074_, v_auxFunName_2075_, v_header_2076_, v_inst_2077_, v_R_2078_, v_a_2079_, v_b_2080_, v_c_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
lean_dec(v___y_2087_);
lean_dec_ref(v___y_2086_);
lean_dec(v___y_2085_);
lean_dec_ref(v___y_2084_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec_ref(v_header_2076_);
lean_dec_ref(v_indVal_2074_);
lean_dec_ref(v_xs_2073_);
lean_dec(v_upperBound_2072_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2(lean_object* v_upperBound_2090_, lean_object* v_inst_2091_, lean_object* v_R_2092_, lean_object* v_a_2093_, lean_object* v_b_2094_, lean_object* v_c_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v___x_2103_; 
v___x_2103_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___redArg(v_upperBound_2090_, v_a_2093_, v_b_2094_, v___y_2100_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2___boxed(lean_object* v_upperBound_2104_, lean_object* v_inst_2105_, lean_object* v_R_2106_, lean_object* v_a_2107_, lean_object* v_b_2108_, lean_object* v_c_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__2(v_upperBound_2104_, v_inst_2105_, v_R_2106_, v_a_2107_, v_b_2108_, v_c_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v_upperBound_2104_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3(lean_object* v_indVal_2118_, lean_object* v_auxFunName_2119_, lean_object* v_header_2120_, lean_object* v_as_2121_, lean_object* v_as_x27_2122_, lean_object* v_b_2123_, lean_object* v_a_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v___x_2132_; 
v___x_2132_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg(v_indVal_2118_, v_auxFunName_2119_, v_header_2120_, v_as_x27_2122_, v_b_2123_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___boxed(lean_object* v_indVal_2133_, lean_object* v_auxFunName_2134_, lean_object* v_header_2135_, lean_object* v_as_2136_, lean_object* v_as_x27_2137_, lean_object* v_b_2138_, lean_object* v_a_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3(v_indVal_2133_, v_auxFunName_2134_, v_header_2135_, v_as_2136_, v_as_x27_2137_, v_b_2138_, v_a_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v_as_x27_2137_);
lean_dec(v_as_2136_);
return v_res_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct(lean_object* v_header_2161_, lean_object* v_indVal_2162_, lean_object* v_auxFunName_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_){
_start:
{
lean_object* v___x_2171_; 
lean_inc_ref(v_indVal_2162_);
lean_inc_ref(v_header_2161_);
v___x_2171_ = l_Lean_Elab_Deriving_mkDiscrs(v_header_2161_, v_indVal_2162_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v___x_2173_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_a_2172_);
lean_dec_ref_known(v___x_2171_, 1);
v___x_2173_ = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts(v_header_2161_, v_indVal_2162_, v_auxFunName_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_, v_a_2169_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2204_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2176_ = v___x_2173_;
v_isShared_2177_ = v_isSharedCheck_2204_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2173_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2204_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v_ref_2178_; uint8_t v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; size_t v_sz_2187_; size_t v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2202_; 
v_ref_2178_ = lean_ctor_get(v_a_2168_, 5);
v___x_2179_ = 0;
v___x_2180_ = l_Lean_SourceInfo_fromRef(v_ref_2178_, v___x_2179_);
v___x_2181_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__0));
v___x_2182_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__1));
lean_inc_n(v___x_2180_, 6);
v___x_2183_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2180_);
lean_ctor_set(v___x_2183_, 1, v___x_2181_);
v___x_2184_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_2185_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22);
v___x_2186_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2180_);
lean_ctor_set(v___x_2186_, 1, v___x_2184_);
lean_ctor_set(v___x_2186_, 2, v___x_2185_);
v_sz_2187_ = lean_array_size(v_a_2172_);
v___x_2188_ = ((size_t)0ULL);
v___x_2189_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__0(v_sz_2187_, v___x_2188_, v_a_2172_);
v___x_2190_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___lam__1___closed__16);
v___x_2191_ = l_Lean_mkSepArray(v___x_2189_, v___x_2190_);
lean_dec_ref(v___x_2189_);
v___x_2192_ = l_Array_append___redArg(v___x_2185_, v___x_2191_);
lean_dec_ref(v___x_2191_);
v___x_2193_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2180_);
lean_ctor_set(v___x_2193_, 1, v___x_2184_);
lean_ctor_set(v___x_2193_, 2, v___x_2192_);
v___x_2194_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__2));
v___x_2195_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2180_);
lean_ctor_set(v___x_2195_, 1, v___x_2194_);
v___x_2196_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkBodyForInduct___closed__4));
v___x_2197_ = l_Array_append___redArg(v___x_2185_, v_a_2174_);
lean_dec(v_a_2174_);
v___x_2198_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2180_);
lean_ctor_set(v___x_2198_, 1, v___x_2184_);
lean_ctor_set(v___x_2198_, 2, v___x_2197_);
v___x_2199_ = l_Lean_Syntax_node1(v___x_2180_, v___x_2196_, v___x_2198_);
lean_inc_ref(v___x_2186_);
v___x_2200_ = l_Lean_Syntax_node6(v___x_2180_, v___x_2182_, v___x_2183_, v___x_2186_, v___x_2186_, v___x_2193_, v___x_2195_, v___x_2199_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 0, v___x_2200_);
v___x_2202_ = v___x_2176_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2200_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
lean_dec(v_a_2172_);
v_a_2205_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___x_2173_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2173_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_dec(v_auxFunName_2163_);
lean_dec_ref(v_indVal_2162_);
lean_dec_ref(v_header_2161_);
v_a_2213_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2171_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2171_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBodyForInduct___boxed(lean_object* v_header_2221_, lean_object* v_indVal_2222_, lean_object* v_auxFunName_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lean_Elab_Deriving_Repr_mkBodyForInduct(v_header_2221_, v_indVal_2222_, v_auxFunName_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
lean_dec(v_a_2225_);
lean_dec_ref(v_a_2224_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBody(lean_object* v_header_2232_, lean_object* v_indVal_2233_, lean_object* v_auxFunName_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_){
_start:
{
lean_object* v___x_2242_; lean_object* v_toConstantVal_2243_; lean_object* v_env_2244_; lean_object* v_name_2245_; uint8_t v___x_2246_; 
v___x_2242_ = lean_st_ref_get(v_a_2240_);
v_toConstantVal_2243_ = lean_ctor_get(v_indVal_2233_, 0);
v_env_2244_ = lean_ctor_get(v___x_2242_, 0);
lean_inc_ref(v_env_2244_);
lean_dec(v___x_2242_);
v_name_2245_ = lean_ctor_get(v_toConstantVal_2243_, 0);
lean_inc(v_name_2245_);
v___x_2246_ = l_Lean_isStructure(v_env_2244_, v_name_2245_);
if (v___x_2246_ == 0)
{
lean_object* v___x_2247_; 
v___x_2247_ = l_Lean_Elab_Deriving_Repr_mkBodyForInduct(v_header_2232_, v_indVal_2233_, v_auxFunName_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
return v___x_2247_;
}
else
{
lean_object* v___x_2248_; 
lean_dec(v_auxFunName_2234_);
v___x_2248_ = l_Lean_Elab_Deriving_Repr_mkBodyForStruct(v_header_2232_, v_indVal_2233_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_a_2240_);
lean_dec_ref(v_header_2232_);
return v___x_2248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkBody___boxed(lean_object* v_header_2249_, lean_object* v_indVal_2250_, lean_object* v_auxFunName_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Lean_Elab_Deriving_Repr_mkBody(v_header_2249_, v_indVal_2250_, v_auxFunName_2251_, v_a_2252_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_);
lean_dec(v_a_2257_);
lean_dec_ref(v_a_2256_);
lean_dec(v_a_2255_);
lean_dec_ref(v_a_2254_);
lean_dec(v_a_2253_);
lean_dec_ref(v_a_2252_);
return v_res_2259_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16(void){
_start:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2300_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__15));
v___x_2301_ = l_String_toRawSubstring_x27(v___x_2300_);
return v___x_2301_;
}
}
static lean_object* _init_l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28(void){
_start:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2330_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__36));
v___x_2331_ = l_String_toRawSubstring_x27(v___x_2330_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction(lean_object* v_ctx_2368_, lean_object* v_i_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_){
_start:
{
lean_object* v_typeInfos_2377_; lean_object* v_auxFunNames_2378_; uint8_t v_usePartial_2379_; lean_object* v___x_2380_; lean_object* v_indVal_2381_; lean_object* v___x_2382_; 
v_typeInfos_2377_ = lean_ctor_get(v_ctx_2368_, 1);
v_auxFunNames_2378_ = lean_ctor_get(v_ctx_2368_, 2);
v_usePartial_2379_ = lean_ctor_get_uint8(v_ctx_2368_, sizeof(void*)*3);
v___x_2380_ = l_Lean_instInhabitedInductiveVal_default;
v_indVal_2381_ = lean_array_get_borrowed(v___x_2380_, v_typeInfos_2377_, v_i_2369_);
lean_inc(v_indVal_2381_);
v___x_2382_ = l_Lean_Elab_Deriving_Repr_mkReprHeader(v_indVal_2381_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2555_; 
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2385_ = v___x_2382_;
v_isShared_2386_ = v_isSharedCheck_2555_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_dec(v___x_2382_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2555_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2387_; lean_object* v_auxFunName_2388_; lean_object* v_body_2390_; lean_object* v___y_2391_; lean_object* v___x_2538_; 
v___x_2387_ = lean_box(0);
v_auxFunName_2388_ = lean_array_get_borrowed(v___x_2387_, v_auxFunNames_2378_, v_i_2369_);
lean_inc(v_auxFunName_2388_);
lean_inc(v_indVal_2381_);
lean_inc(v_a_2383_);
v___x_2538_ = l_Lean_Elab_Deriving_Repr_mkBody(v_a_2383_, v_indVal_2381_, v_auxFunName_2388_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_);
if (lean_obj_tag(v___x_2538_) == 0)
{
if (v_usePartial_2379_ == 0)
{
lean_object* v_a_2539_; 
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_a_2539_);
lean_dec_ref_known(v___x_2538_, 1);
v_body_2390_ = v_a_2539_;
v___y_2391_ = v_a_2374_;
goto v___jp_2389_;
}
else
{
lean_object* v_a_2540_; lean_object* v_argNames_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v_a_2540_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_a_2540_);
lean_dec_ref_known(v___x_2538_, 1);
v_argNames_2541_ = lean_ctor_get(v_a_2383_, 1);
v___x_2542_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1));
lean_inc_ref(v_argNames_2541_);
v___x_2543_ = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(v_ctx_2368_, v___x_2542_, v_argNames_2541_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; lean_object* v___x_2545_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_a_2544_);
lean_dec_ref_known(v___x_2543_, 1);
v___x_2545_ = l_Lean_Elab_Deriving_mkLet(v_a_2544_, v_a_2540_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_);
lean_dec(v_a_2544_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; 
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_a_2546_);
lean_dec_ref_known(v___x_2545_, 1);
v_body_2390_ = v_a_2546_;
v___y_2391_ = v_a_2374_;
goto v___jp_2389_;
}
else
{
lean_del_object(v___x_2385_);
lean_dec(v_a_2383_);
return v___x_2545_;
}
}
else
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2554_; 
lean_dec(v_a_2540_);
lean_del_object(v___x_2385_);
lean_dec(v_a_2383_);
v_a_2547_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2549_ = v___x_2543_;
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2543_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2552_; 
if (v_isShared_2550_ == 0)
{
v___x_2552_ = v___x_2549_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_a_2547_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
}
}
else
{
lean_del_object(v___x_2385_);
lean_dec(v_a_2383_);
return v___x_2538_;
}
v___jp_2389_:
{
if (v_usePartial_2379_ == 0)
{
lean_object* v_binders_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2458_; 
v_binders_2392_ = lean_ctor_get(v_a_2383_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v_a_2383_);
if (v_isSharedCheck_2458_ == 0)
{
lean_object* v_unused_2459_; lean_object* v_unused_2460_; lean_object* v_unused_2461_; 
v_unused_2459_ = lean_ctor_get(v_a_2383_, 3);
lean_dec(v_unused_2459_);
v_unused_2460_ = lean_ctor_get(v_a_2383_, 2);
lean_dec(v_unused_2460_);
v_unused_2461_ = lean_ctor_get(v_a_2383_, 1);
lean_dec(v_unused_2461_);
v___x_2394_ = v_a_2383_;
v_isShared_2395_ = v_isSharedCheck_2458_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_binders_2392_);
lean_dec(v_a_2383_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2458_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v_ref_2396_; lean_object* v_quotContext_2397_; lean_object* v_currMacroScope_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2417_; 
v_ref_2396_ = lean_ctor_get(v___y_2391_, 5);
v_quotContext_2397_ = lean_ctor_get(v___y_2391_, 10);
v_currMacroScope_2398_ = lean_ctor_get(v___y_2391_, 11);
v___x_2399_ = l_Lean_SourceInfo_fromRef(v_ref_2396_, v_usePartial_2379_);
v___x_2400_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2));
v___x_2401_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4));
v___x_2402_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_2403_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22);
lean_inc_n(v___x_2399_, 4);
v___x_2404_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2399_);
lean_ctor_set(v___x_2404_, 1, v___x_2402_);
lean_ctor_set(v___x_2404_, 2, v___x_2403_);
v___x_2405_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6));
v___x_2406_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__7));
v___x_2407_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2399_);
lean_ctor_set(v___x_2407_, 1, v___x_2406_);
v___x_2408_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9));
v___x_2409_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11));
lean_inc_ref(v___x_2404_);
v___x_2410_ = l_Lean_Syntax_node1(v___x_2399_, v___x_2409_, v___x_2404_);
v___x_2411_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14));
v___x_2412_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16, &l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16_once, _init_l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16);
v___x_2413_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__17));
lean_inc(v_currMacroScope_2398_);
lean_inc(v_quotContext_2397_);
v___x_2414_ = l_Lean_addMacroScope(v_quotContext_2397_, v___x_2413_, v_currMacroScope_2398_);
v___x_2415_ = lean_box(0);
if (v_isShared_2395_ == 0)
{
lean_ctor_set_tag(v___x_2394_, 3);
lean_ctor_set(v___x_2394_, 3, v___x_2415_);
lean_ctor_set(v___x_2394_, 2, v___x_2414_);
lean_ctor_set(v___x_2394_, 1, v___x_2412_);
lean_ctor_set(v___x_2394_, 0, v___x_2399_);
v___x_2417_ = v___x_2394_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v___x_2399_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v___x_2412_);
lean_ctor_set(v_reuseFailAlloc_2457_, 2, v___x_2414_);
lean_ctor_set(v_reuseFailAlloc_2457_, 3, v___x_2415_);
v___x_2417_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2455_; 
lean_inc_ref_n(v___x_2404_, 11);
lean_inc_n(v___x_2399_, 19);
v___x_2418_ = l_Lean_Syntax_node2(v___x_2399_, v___x_2411_, v___x_2417_, v___x_2404_);
v___x_2419_ = l_Lean_Syntax_node2(v___x_2399_, v___x_2408_, v___x_2410_, v___x_2418_);
v___x_2420_ = l_Lean_Syntax_node1(v___x_2399_, v___x_2402_, v___x_2419_);
v___x_2421_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__18));
v___x_2422_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2399_);
lean_ctor_set(v___x_2422_, 1, v___x_2421_);
v___x_2423_ = l_Lean_Syntax_node3(v___x_2399_, v___x_2405_, v___x_2407_, v___x_2420_, v___x_2422_);
v___x_2424_ = l_Lean_Syntax_node1(v___x_2399_, v___x_2402_, v___x_2423_);
v___x_2425_ = l_Lean_Syntax_node7(v___x_2399_, v___x_2401_, v___x_2404_, v___x_2424_, v___x_2404_, v___x_2404_, v___x_2404_, v___x_2404_, v___x_2404_);
v___x_2426_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20));
v___x_2427_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__21));
v___x_2428_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2428_, 0, v___x_2399_);
lean_ctor_set(v___x_2428_, 1, v___x_2427_);
v___x_2429_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23));
lean_inc(v_auxFunName_2388_);
v___x_2430_ = lean_mk_syntax_ident(v_auxFunName_2388_);
v___x_2431_ = l_Lean_Syntax_node2(v___x_2399_, v___x_2429_, v___x_2430_, v___x_2404_);
v___x_2432_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25));
v___x_2433_ = l_Array_append___redArg(v___x_2403_, v_binders_2392_);
lean_dec_ref(v_binders_2392_);
v___x_2434_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2399_);
lean_ctor_set(v___x_2434_, 1, v___x_2402_);
lean_ctor_set(v___x_2434_, 2, v___x_2433_);
v___x_2435_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27));
v___x_2436_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__13));
v___x_2437_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2399_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
v___x_2438_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28, &l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28_once, _init_l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28);
v___x_2439_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__29));
lean_inc(v_currMacroScope_2398_);
lean_inc(v_quotContext_2397_);
v___x_2440_ = l_Lean_addMacroScope(v_quotContext_2397_, v___x_2439_, v_currMacroScope_2398_);
v___x_2441_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__34));
v___x_2442_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2399_);
lean_ctor_set(v___x_2442_, 1, v___x_2438_);
lean_ctor_set(v___x_2442_, 2, v___x_2440_);
lean_ctor_set(v___x_2442_, 3, v___x_2441_);
v___x_2443_ = l_Lean_Syntax_node2(v___x_2399_, v___x_2435_, v___x_2437_, v___x_2442_);
v___x_2444_ = l_Lean_Syntax_node1(v___x_2399_, v___x_2402_, v___x_2443_);
v___x_2445_ = l_Lean_Syntax_node2(v___x_2399_, v___x_2432_, v___x_2434_, v___x_2444_);
v___x_2446_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36));
v___x_2447_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__37));
v___x_2448_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2399_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
v___x_2449_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40));
v___x_2450_ = l_Lean_Syntax_node2(v___x_2399_, v___x_2449_, v___x_2404_, v___x_2404_);
v___x_2451_ = l_Lean_Syntax_node4(v___x_2399_, v___x_2446_, v___x_2448_, v_body_2390_, v___x_2450_, v___x_2404_);
v___x_2452_ = l_Lean_Syntax_node5(v___x_2399_, v___x_2426_, v___x_2428_, v___x_2431_, v___x_2445_, v___x_2451_, v___x_2404_);
v___x_2453_ = l_Lean_Syntax_node2(v___x_2399_, v___x_2400_, v___x_2425_, v___x_2452_);
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 0, v___x_2453_);
v___x_2455_ = v___x_2385_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2453_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
else
{
lean_object* v_binders_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2534_; 
v_binders_2462_ = lean_ctor_get(v_a_2383_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v_a_2383_);
if (v_isSharedCheck_2534_ == 0)
{
lean_object* v_unused_2535_; lean_object* v_unused_2536_; lean_object* v_unused_2537_; 
v_unused_2535_ = lean_ctor_get(v_a_2383_, 3);
lean_dec(v_unused_2535_);
v_unused_2536_ = lean_ctor_get(v_a_2383_, 2);
lean_dec(v_unused_2536_);
v_unused_2537_ = lean_ctor_get(v_a_2383_, 1);
lean_dec(v_unused_2537_);
v___x_2464_ = v_a_2383_;
v_isShared_2465_ = v_isSharedCheck_2534_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_binders_2462_);
lean_dec(v_a_2383_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2534_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v_ref_2466_; lean_object* v_quotContext_2467_; lean_object* v_currMacroScope_2468_; uint8_t v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2488_; 
v_ref_2466_ = lean_ctor_get(v___y_2391_, 5);
v_quotContext_2467_ = lean_ctor_get(v___y_2391_, 10);
v_currMacroScope_2468_ = lean_ctor_get(v___y_2391_, 11);
v___x_2469_ = 0;
v___x_2470_ = l_Lean_SourceInfo_fromRef(v_ref_2466_, v___x_2469_);
v___x_2471_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__2));
v___x_2472_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__4));
v___x_2473_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_2474_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22);
lean_inc_n(v___x_2470_, 4);
v___x_2475_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2470_);
lean_ctor_set(v___x_2475_, 1, v___x_2473_);
lean_ctor_set(v___x_2475_, 2, v___x_2474_);
v___x_2476_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__6));
v___x_2477_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__7));
v___x_2478_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2470_);
lean_ctor_set(v___x_2478_, 1, v___x_2477_);
v___x_2479_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__9));
v___x_2480_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__11));
lean_inc_ref(v___x_2475_);
v___x_2481_ = l_Lean_Syntax_node1(v___x_2470_, v___x_2480_, v___x_2475_);
v___x_2482_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__14));
v___x_2483_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16, &l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16_once, _init_l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__16);
v___x_2484_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__17));
lean_inc(v_currMacroScope_2468_);
lean_inc(v_quotContext_2467_);
v___x_2485_ = l_Lean_addMacroScope(v_quotContext_2467_, v___x_2484_, v_currMacroScope_2468_);
v___x_2486_ = lean_box(0);
if (v_isShared_2465_ == 0)
{
lean_ctor_set_tag(v___x_2464_, 3);
lean_ctor_set(v___x_2464_, 3, v___x_2486_);
lean_ctor_set(v___x_2464_, 2, v___x_2485_);
lean_ctor_set(v___x_2464_, 1, v___x_2483_);
lean_ctor_set(v___x_2464_, 0, v___x_2470_);
v___x_2488_ = v___x_2464_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2470_);
lean_ctor_set(v_reuseFailAlloc_2533_, 1, v___x_2483_);
lean_ctor_set(v_reuseFailAlloc_2533_, 2, v___x_2485_);
lean_ctor_set(v_reuseFailAlloc_2533_, 3, v___x_2486_);
v___x_2488_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2531_; 
lean_inc_ref_n(v___x_2475_, 10);
lean_inc_n(v___x_2470_, 22);
v___x_2489_ = l_Lean_Syntax_node2(v___x_2470_, v___x_2482_, v___x_2488_, v___x_2475_);
v___x_2490_ = l_Lean_Syntax_node2(v___x_2470_, v___x_2479_, v___x_2481_, v___x_2489_);
v___x_2491_ = l_Lean_Syntax_node1(v___x_2470_, v___x_2473_, v___x_2490_);
v___x_2492_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__18));
v___x_2493_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2470_);
lean_ctor_set(v___x_2493_, 1, v___x_2492_);
v___x_2494_ = l_Lean_Syntax_node3(v___x_2470_, v___x_2476_, v___x_2478_, v___x_2491_, v___x_2493_);
v___x_2495_ = l_Lean_Syntax_node1(v___x_2470_, v___x_2473_, v___x_2494_);
v___x_2496_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__41));
v___x_2497_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__42));
v___x_2498_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2470_);
lean_ctor_set(v___x_2498_, 1, v___x_2496_);
v___x_2499_ = l_Lean_Syntax_node1(v___x_2470_, v___x_2497_, v___x_2498_);
v___x_2500_ = l_Lean_Syntax_node1(v___x_2470_, v___x_2473_, v___x_2499_);
v___x_2501_ = l_Lean_Syntax_node7(v___x_2470_, v___x_2472_, v___x_2475_, v___x_2495_, v___x_2475_, v___x_2475_, v___x_2475_, v___x_2475_, v___x_2500_);
v___x_2502_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__20));
v___x_2503_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__21));
v___x_2504_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2470_);
lean_ctor_set(v___x_2504_, 1, v___x_2503_);
v___x_2505_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__23));
lean_inc(v_auxFunName_2388_);
v___x_2506_ = lean_mk_syntax_ident(v_auxFunName_2388_);
v___x_2507_ = l_Lean_Syntax_node2(v___x_2470_, v___x_2505_, v___x_2506_, v___x_2475_);
v___x_2508_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__25));
v___x_2509_ = l_Array_append___redArg(v___x_2474_, v_binders_2462_);
lean_dec_ref(v_binders_2462_);
v___x_2510_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2510_, 0, v___x_2470_);
lean_ctor_set(v___x_2510_, 1, v___x_2473_);
lean_ctor_set(v___x_2510_, 2, v___x_2509_);
v___x_2511_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__27));
v___x_2512_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__13));
v___x_2513_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2470_);
lean_ctor_set(v___x_2513_, 1, v___x_2512_);
v___x_2514_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28, &l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28_once, _init_l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__28);
v___x_2515_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__29));
lean_inc(v_currMacroScope_2468_);
lean_inc(v_quotContext_2467_);
v___x_2516_ = l_Lean_addMacroScope(v_quotContext_2467_, v___x_2515_, v_currMacroScope_2468_);
v___x_2517_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__34));
v___x_2518_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2470_);
lean_ctor_set(v___x_2518_, 1, v___x_2514_);
lean_ctor_set(v___x_2518_, 2, v___x_2516_);
lean_ctor_set(v___x_2518_, 3, v___x_2517_);
v___x_2519_ = l_Lean_Syntax_node2(v___x_2470_, v___x_2511_, v___x_2513_, v___x_2518_);
v___x_2520_ = l_Lean_Syntax_node1(v___x_2470_, v___x_2473_, v___x_2519_);
v___x_2521_ = l_Lean_Syntax_node2(v___x_2470_, v___x_2508_, v___x_2510_, v___x_2520_);
v___x_2522_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__36));
v___x_2523_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__37));
v___x_2524_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2470_);
lean_ctor_set(v___x_2524_, 1, v___x_2523_);
v___x_2525_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkAuxFunction___closed__40));
v___x_2526_ = l_Lean_Syntax_node2(v___x_2470_, v___x_2525_, v___x_2475_, v___x_2475_);
v___x_2527_ = l_Lean_Syntax_node4(v___x_2470_, v___x_2522_, v___x_2524_, v_body_2390_, v___x_2526_, v___x_2475_);
v___x_2528_ = l_Lean_Syntax_node5(v___x_2470_, v___x_2502_, v___x_2504_, v___x_2507_, v___x_2521_, v___x_2527_, v___x_2475_);
v___x_2529_ = l_Lean_Syntax_node2(v___x_2470_, v___x_2471_, v___x_2501_, v___x_2528_);
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 0, v___x_2529_);
v___x_2531_ = v___x_2385_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2529_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
v_a_2556_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v___x_2382_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2382_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkAuxFunction___boxed(lean_object* v_ctx_2564_, lean_object* v_i_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction(v_ctx_2564_, v_i_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_);
lean_dec(v_a_2571_);
lean_dec_ref(v_a_2570_);
lean_dec(v_a_2569_);
lean_dec_ref(v_a_2568_);
lean_dec(v_a_2567_);
lean_dec_ref(v_a_2566_);
lean_dec(v_i_2565_);
lean_dec_ref(v_ctx_2564_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg(lean_object* v_upperBound_2574_, lean_object* v_ctx_2575_, lean_object* v_a_2576_, lean_object* v_b_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
uint8_t v___x_2585_; 
v___x_2585_ = lean_nat_dec_lt(v_a_2576_, v_upperBound_2574_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2586_; 
lean_dec(v_a_2576_);
v___x_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2586_, 0, v_b_2577_);
return v___x_2586_;
}
else
{
lean_object* v___x_2587_; 
v___x_2587_ = l_Lean_Elab_Deriving_Repr_mkAuxFunction(v_ctx_2575_, v_a_2576_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
lean_inc(v_a_2588_);
lean_dec_ref_known(v___x_2587_, 1);
v___x_2589_ = lean_array_push(v_b_2577_, v_a_2588_);
v___x_2590_ = lean_unsigned_to_nat(1u);
v___x_2591_ = lean_nat_add(v_a_2576_, v___x_2590_);
lean_dec(v_a_2576_);
v_a_2576_ = v___x_2591_;
v_b_2577_ = v___x_2589_;
goto _start;
}
else
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2600_; 
lean_dec_ref(v_b_2577_);
lean_dec(v_a_2576_);
v_a_2593_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2595_ = v___x_2587_;
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2587_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2598_; 
if (v_isShared_2596_ == 0)
{
v___x_2598_ = v___x_2595_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2593_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg___boxed(lean_object* v_upperBound_2601_, lean_object* v_ctx_2602_, lean_object* v_a_2603_, lean_object* v_b_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg(v_upperBound_2601_, v_ctx_2602_, v_a_2603_, v_b_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v_ctx_2602_);
lean_dec(v_upperBound_2601_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkMutualBlock(lean_object* v_ctx_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_){
_start:
{
lean_object* v_typeInfos_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v_auxDefs_2631_; lean_object* v___x_2632_; 
v_typeInfos_2628_ = lean_ctor_get(v_ctx_2620_, 1);
v___x_2629_ = lean_array_get_size(v_typeInfos_2628_);
v___x_2630_ = lean_unsigned_to_nat(0u);
v_auxDefs_2631_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkBodyForInduct_mkAlts_spec__3___redArg___closed__1));
v___x_2632_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg(v___x_2629_, v_ctx_2620_, v___x_2630_, v_auxDefs_2631_, v_a_2621_, v_a_2622_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_);
if (lean_obj_tag(v___x_2632_) == 0)
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2653_; 
v_a_2633_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2635_ = v___x_2632_;
v_isShared_2636_ = v_isSharedCheck_2653_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2632_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2653_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v_ref_2637_; uint8_t v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2651_; 
v_ref_2637_ = lean_ctor_get(v_a_2625_, 5);
v___x_2638_ = 0;
v___x_2639_ = l_Lean_SourceInfo_fromRef(v_ref_2637_, v___x_2638_);
v___x_2640_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__0));
v___x_2641_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__1));
lean_inc_n(v___x_2639_, 3);
v___x_2642_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2639_);
lean_ctor_set(v___x_2642_, 1, v___x_2640_);
v___x_2643_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__9));
v___x_2644_ = lean_obj_once(&l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22, &l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22_once, _init_l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__22);
v___x_2645_ = l_Array_append___redArg(v___x_2644_, v_a_2633_);
lean_dec(v_a_2633_);
v___x_2646_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2639_);
lean_ctor_set(v___x_2646_, 1, v___x_2643_);
lean_ctor_set(v___x_2646_, 2, v___x_2645_);
v___x_2647_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkMutualBlock___closed__2));
v___x_2648_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2639_);
lean_ctor_set(v___x_2648_, 1, v___x_2647_);
v___x_2649_ = l_Lean_Syntax_node3(v___x_2639_, v___x_2641_, v___x_2642_, v___x_2646_, v___x_2648_);
if (v_isShared_2636_ == 0)
{
lean_ctor_set(v___x_2635_, 0, v___x_2649_);
v___x_2651_ = v___x_2635_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2649_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
v_a_2654_ = lean_ctor_get(v___x_2632_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2632_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2632_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2632_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkMutualBlock___boxed(lean_object* v_ctx_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l_Lean_Elab_Deriving_Repr_mkMutualBlock(v_ctx_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
lean_dec(v_a_2668_);
lean_dec_ref(v_a_2667_);
lean_dec(v_a_2666_);
lean_dec_ref(v_a_2665_);
lean_dec(v_a_2664_);
lean_dec_ref(v_a_2663_);
lean_dec_ref(v_ctx_2662_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0(lean_object* v_upperBound_2671_, lean_object* v_ctx_2672_, lean_object* v_inst_2673_, lean_object* v_R_2674_, lean_object* v_a_2675_, lean_object* v_b_2676_, lean_object* v_c_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
lean_object* v___x_2685_; 
v___x_2685_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___redArg(v_upperBound_2671_, v_ctx_2672_, v_a_2675_, v_b_2676_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0___boxed(lean_object* v_upperBound_2686_, lean_object* v_ctx_2687_, lean_object* v_inst_2688_, lean_object* v_R_2689_, lean_object* v_a_2690_, lean_object* v_b_2691_, lean_object* v_c_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkMutualBlock_spec__0(v_upperBound_2686_, v_ctx_2687_, v_inst_2688_, v_R_2689_, v_a_2690_, v_b_2691_, v_c_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec_ref(v_ctx_2687_);
lean_dec(v_upperBound_2686_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__0(lean_object* v_a_2701_, lean_object* v_a_2702_){
_start:
{
if (lean_obj_tag(v_a_2701_) == 0)
{
lean_object* v___x_2703_; 
v___x_2703_ = l_List_reverse___redArg(v_a_2702_);
return v___x_2703_;
}
else
{
lean_object* v_head_2704_; lean_object* v_tail_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2714_; 
v_head_2704_ = lean_ctor_get(v_a_2701_, 0);
v_tail_2705_ = lean_ctor_get(v_a_2701_, 1);
v_isSharedCheck_2714_ = !lean_is_exclusive(v_a_2701_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2707_ = v_a_2701_;
v_isShared_2708_ = v_isSharedCheck_2714_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_tail_2705_);
lean_inc(v_head_2704_);
lean_dec(v_a_2701_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2714_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2709_; lean_object* v___x_2711_; 
v___x_2709_ = l_Lean_MessageData_ofSyntax(v_head_2704_);
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 1, v_a_2702_);
lean_ctor_set(v___x_2707_, 0, v___x_2709_);
v___x_2711_ = v___x_2707_;
goto v_reusejp_2710_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2709_);
lean_ctor_set(v_reuseFailAlloc_2713_, 1, v_a_2702_);
v___x_2711_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2710_;
}
v_reusejp_2710_:
{
v_a_2701_ = v_tail_2705_;
v_a_2702_ = v___x_2711_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2715_; double v___x_2716_; 
v___x_2715_ = lean_unsigned_to_nat(0u);
v___x_2716_ = lean_float_of_nat(v___x_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg(lean_object* v_cls_2719_, lean_object* v_msg_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v_ref_2726_; lean_object* v___x_2727_; lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2772_; 
v_ref_2726_ = lean_ctor_get(v___y_2723_, 5);
v___x_2727_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__3_spec__4(v_msg_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
v_a_2728_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2730_ = v___x_2727_;
v_isShared_2731_ = v_isSharedCheck_2772_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2727_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2772_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2732_; lean_object* v_traceState_2733_; lean_object* v_env_2734_; lean_object* v_nextMacroScope_2735_; lean_object* v_ngen_2736_; lean_object* v_auxDeclNGen_2737_; lean_object* v_cache_2738_; lean_object* v_messages_2739_; lean_object* v_infoState_2740_; lean_object* v_snapshotTasks_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2771_; 
v___x_2732_ = lean_st_ref_take(v___y_2724_);
v_traceState_2733_ = lean_ctor_get(v___x_2732_, 4);
v_env_2734_ = lean_ctor_get(v___x_2732_, 0);
v_nextMacroScope_2735_ = lean_ctor_get(v___x_2732_, 1);
v_ngen_2736_ = lean_ctor_get(v___x_2732_, 2);
v_auxDeclNGen_2737_ = lean_ctor_get(v___x_2732_, 3);
v_cache_2738_ = lean_ctor_get(v___x_2732_, 5);
v_messages_2739_ = lean_ctor_get(v___x_2732_, 6);
v_infoState_2740_ = lean_ctor_get(v___x_2732_, 7);
v_snapshotTasks_2741_ = lean_ctor_get(v___x_2732_, 8);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2743_ = v___x_2732_;
v_isShared_2744_ = v_isSharedCheck_2771_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_snapshotTasks_2741_);
lean_inc(v_infoState_2740_);
lean_inc(v_messages_2739_);
lean_inc(v_cache_2738_);
lean_inc(v_traceState_2733_);
lean_inc(v_auxDeclNGen_2737_);
lean_inc(v_ngen_2736_);
lean_inc(v_nextMacroScope_2735_);
lean_inc(v_env_2734_);
lean_dec(v___x_2732_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2771_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
uint64_t v_tid_2745_; lean_object* v_traces_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2770_; 
v_tid_2745_ = lean_ctor_get_uint64(v_traceState_2733_, sizeof(void*)*1);
v_traces_2746_ = lean_ctor_get(v_traceState_2733_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v_traceState_2733_);
if (v_isSharedCheck_2770_ == 0)
{
v___x_2748_ = v_traceState_2733_;
v_isShared_2749_ = v_isSharedCheck_2770_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_traces_2746_);
lean_dec(v_traceState_2733_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2770_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2750_; double v___x_2751_; uint8_t v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2760_; 
v___x_2750_ = lean_box(0);
v___x_2751_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__0);
v___x_2752_ = 0;
v___x_2753_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__14));
v___x_2754_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2754_, 0, v_cls_2719_);
lean_ctor_set(v___x_2754_, 1, v___x_2750_);
lean_ctor_set(v___x_2754_, 2, v___x_2753_);
lean_ctor_set_float(v___x_2754_, sizeof(void*)*3, v___x_2751_);
lean_ctor_set_float(v___x_2754_, sizeof(void*)*3 + 8, v___x_2751_);
lean_ctor_set_uint8(v___x_2754_, sizeof(void*)*3 + 16, v___x_2752_);
v___x_2755_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___closed__1));
v___x_2756_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2754_);
lean_ctor_set(v___x_2756_, 1, v_a_2728_);
lean_ctor_set(v___x_2756_, 2, v___x_2755_);
lean_inc(v_ref_2726_);
v___x_2757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2757_, 0, v_ref_2726_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
v___x_2758_ = l_Lean_PersistentArray_push___redArg(v_traces_2746_, v___x_2757_);
if (v_isShared_2749_ == 0)
{
lean_ctor_set(v___x_2748_, 0, v___x_2758_);
v___x_2760_ = v___x_2748_;
goto v_reusejp_2759_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2758_);
lean_ctor_set_uint64(v_reuseFailAlloc_2769_, sizeof(void*)*1, v_tid_2745_);
v___x_2760_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2759_;
}
v_reusejp_2759_:
{
lean_object* v___x_2762_; 
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 4, v___x_2760_);
v___x_2762_ = v___x_2743_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_env_2734_);
lean_ctor_set(v_reuseFailAlloc_2768_, 1, v_nextMacroScope_2735_);
lean_ctor_set(v_reuseFailAlloc_2768_, 2, v_ngen_2736_);
lean_ctor_set(v_reuseFailAlloc_2768_, 3, v_auxDeclNGen_2737_);
lean_ctor_set(v_reuseFailAlloc_2768_, 4, v___x_2760_);
lean_ctor_set(v_reuseFailAlloc_2768_, 5, v_cache_2738_);
lean_ctor_set(v_reuseFailAlloc_2768_, 6, v_messages_2739_);
lean_ctor_set(v_reuseFailAlloc_2768_, 7, v_infoState_2740_);
lean_ctor_set(v_reuseFailAlloc_2768_, 8, v_snapshotTasks_2741_);
v___x_2762_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2766_; 
v___x_2763_ = lean_st_ref_set(v___y_2724_, v___x_2762_);
v___x_2764_ = lean_box(0);
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 0, v___x_2764_);
v___x_2766_ = v___x_2730_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v___x_2764_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
return v___x_2766_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg___boxed(lean_object* v_cls_2773_, lean_object* v_msg_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg(v_cls_2773_, v_msg_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
return v_res_2780_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__3(void){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2788_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0));
v___x_2789_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__2));
v___x_2790_ = l_Lean_Name_append(v___x_2789_, v___x_2788_);
return v___x_2790_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__5(void){
_start:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2792_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__4));
v___x_2793_ = l_Lean_stringToMessageData(v___x_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd(lean_object* v_declName_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_){
_start:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; uint8_t v___x_2804_; lean_object* v___x_2805_; 
v___x_2802_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1));
v___x_2803_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Deriving_Repr_mkBodyForStruct_spec__2___redArg___lam__1___closed__53));
v___x_2804_ = 1;
lean_inc(v_declName_2794_);
v___x_2805_ = l_Lean_Elab_Deriving_mkContext(v___x_2802_, v___x_2803_, v_declName_2794_, v___x_2804_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v_a_2806_; lean_object* v___x_2807_; 
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_a_2806_);
lean_dec_ref_known(v___x_2805_, 1);
v___x_2807_ = l_Lean_Elab_Deriving_Repr_mkMutualBlock(v_a_2806_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref_known(v___x_2807_, 1);
v___x_2809_ = lean_unsigned_to_nat(1u);
v___x_2810_ = lean_mk_empty_array_with_capacity(v___x_2809_);
lean_inc_ref(v___x_2810_);
v___x_2811_ = lean_array_push(v___x_2810_, v_declName_2794_);
v___x_2812_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_a_2806_, v___x_2802_, v___x_2811_, v___x_2804_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_);
lean_dec_ref(v___x_2811_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_options_2813_; lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2854_; 
v_options_2813_ = lean_ctor_get(v_a_2799_, 2);
v_a_2814_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2816_ = v___x_2812_;
v_isShared_2817_ = v_isSharedCheck_2854_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_a_2814_);
lean_dec(v___x_2812_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2854_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v_inheritedTraceOptions_2818_; uint8_t v_hasTrace_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v_inheritedTraceOptions_2818_ = lean_ctor_get(v_a_2799_, 13);
v_hasTrace_2819_ = lean_ctor_get_uint8(v_options_2813_, sizeof(void*)*1);
v___x_2820_ = lean_array_push(v___x_2810_, v_a_2808_);
v___x_2821_ = l_Array_append___redArg(v___x_2820_, v_a_2814_);
lean_dec(v_a_2814_);
if (v_hasTrace_2819_ == 0)
{
lean_object* v___x_2823_; 
if (v_isShared_2817_ == 0)
{
lean_ctor_set(v___x_2816_, 0, v___x_2821_);
v___x_2823_ = v___x_2816_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v___x_2821_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
else
{
lean_object* v___x_2825_; lean_object* v___x_2826_; uint8_t v___x_2827_; 
v___x_2825_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0));
v___x_2826_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__3, &l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__3_once, _init_l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__3);
v___x_2827_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2818_, v_options_2813_, v___x_2826_);
if (v___x_2827_ == 0)
{
lean_object* v___x_2829_; 
if (v_isShared_2817_ == 0)
{
lean_ctor_set(v___x_2816_, 0, v___x_2821_);
v___x_2829_ = v___x_2816_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v___x_2821_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
else
{
lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
lean_del_object(v___x_2816_);
v___x_2831_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__5, &l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__5_once, _init_l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__5);
lean_inc_ref(v___x_2821_);
v___x_2832_ = lean_array_to_list(v___x_2821_);
v___x_2833_ = lean_box(0);
v___x_2834_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__0(v___x_2832_, v___x_2833_);
v___x_2835_ = l_Lean_MessageData_ofList(v___x_2834_);
v___x_2836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2831_);
lean_ctor_set(v___x_2836_, 1, v___x_2835_);
v___x_2837_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg(v___x_2825_, v___x_2836_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2844_; 
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2844_ == 0)
{
lean_object* v_unused_2845_; 
v_unused_2845_ = lean_ctor_get(v___x_2837_, 0);
lean_dec(v_unused_2845_);
v___x_2839_ = v___x_2837_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_dec(v___x_2837_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2842_; 
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 0, v___x_2821_);
v___x_2842_ = v___x_2839_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2821_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
else
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
lean_dec_ref(v___x_2821_);
v_a_2846_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2848_ = v___x_2837_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2837_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2851_; 
if (v_isShared_2849_ == 0)
{
v___x_2851_ = v___x_2848_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_a_2846_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
lean_dec_ref(v___x_2810_);
lean_dec(v_a_2808_);
v_a_2855_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2857_ = v___x_2812_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2812_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2858_ == 0)
{
v___x_2860_ = v___x_2857_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2855_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
else
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2870_; 
lean_dec(v_a_2806_);
lean_dec(v_declName_2794_);
v_a_2863_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v___x_2807_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2807_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
else
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
lean_dec(v_declName_2794_);
v_a_2871_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2805_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2805_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___boxed(lean_object* v_declName_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_){
_start:
{
lean_object* v_res_2887_; 
v_res_2887_ = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd(v_declName_2879_, v_a_2880_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_);
lean_dec(v_a_2885_);
lean_dec_ref(v_a_2884_);
lean_dec(v_a_2883_);
lean_dec_ref(v_a_2882_);
lean_dec(v_a_2881_);
lean_dec_ref(v_a_2880_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1(lean_object* v_cls_2888_, lean_object* v_msg_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_){
_start:
{
lean_object* v___x_2897_; 
v___x_2897_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___redArg(v_cls_2888_, v_msg_2889_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1___boxed(lean_object* v_cls_2898_, lean_object* v_msg_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd_spec__1(v_cls_2898_, v_msg_2899_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
lean_dec(v___y_2901_);
lean_dec_ref(v___y_2900_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg(lean_object* v_declName_2908_, lean_object* v___y_2909_){
_start:
{
lean_object* v___x_2911_; lean_object* v_env_2912_; uint8_t v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2911_ = lean_st_ref_get(v___y_2909_);
v_env_2912_ = lean_ctor_get(v___x_2911_, 0);
lean_inc_ref(v_env_2912_);
lean_dec(v___x_2911_);
v___x_2913_ = l_Lean_isInductiveCore(v_env_2912_, v_declName_2908_);
v___x_2914_ = lean_box(v___x_2913_);
v___x_2915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2914_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg___boxed(lean_object* v_declName_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg(v_declName_2916_, v___y_2917_);
lean_dec(v___y_2917_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0(lean_object* v_declName_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v___x_2924_; 
v___x_2924_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg(v_declName_2920_, v___y_2922_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___boxed(lean_object* v_declName_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0(v_declName_2925_, v___y_2926_, v___y_2927_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0(uint8_t v_____do__lift_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
if (v_____do__lift_2930_ == 0)
{
uint8_t v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2934_ = 1;
v___x_2935_ = lean_box(v___x_2934_);
v___x_2936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2935_);
return v___x_2936_;
}
else
{
uint8_t v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2937_ = 0;
v___x_2938_ = lean_box(v___x_2937_);
v___x_2939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2938_);
return v___x_2939_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_){
_start:
{
uint8_t v_____do__lift_2462__boxed_2944_; lean_object* v_res_2945_; 
v_____do__lift_2462__boxed_2944_ = lean_unbox(v_____do__lift_2940_);
v_res_2945_ = l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0(v_____do__lift_2462__boxed_2944_, v___y_2941_, v___y_2942_);
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2941_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1(lean_object* v_as_2946_, size_t v_i_2947_, size_t v_stop_2948_, lean_object* v_b_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_){
_start:
{
uint8_t v___x_2953_; 
v___x_2953_ = lean_usize_dec_eq(v_i_2947_, v_stop_2948_);
if (v___x_2953_ == 0)
{
lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2954_ = lean_array_uget_borrowed(v_as_2946_, v_i_2947_);
lean_inc(v___x_2954_);
v___x_2955_ = l_Lean_Elab_Command_elabCommand(v___x_2954_, v___y_2950_, v___y_2951_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; size_t v___x_2957_; size_t v___x_2958_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
lean_inc(v_a_2956_);
lean_dec_ref_known(v___x_2955_, 1);
v___x_2957_ = ((size_t)1ULL);
v___x_2958_ = lean_usize_add(v_i_2947_, v___x_2957_);
v_i_2947_ = v___x_2958_;
v_b_2949_ = v_a_2956_;
goto _start;
}
else
{
return v___x_2955_;
}
}
else
{
lean_object* v___x_2960_; 
v___x_2960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2960_, 0, v_b_2949_);
return v___x_2960_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1___boxed(lean_object* v_as_2961_, lean_object* v_i_2962_, lean_object* v_stop_2963_, lean_object* v_b_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
size_t v_i_boxed_2968_; size_t v_stop_boxed_2969_; lean_object* v_res_2970_; 
v_i_boxed_2968_ = lean_unbox_usize(v_i_2962_);
lean_dec(v_i_2962_);
v_stop_boxed_2969_ = lean_unbox_usize(v_stop_2963_);
lean_dec(v_stop_2963_);
v_res_2970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1(v_as_2961_, v_i_boxed_2968_, v_stop_boxed_2969_, v_b_2964_, v___y_2965_, v___y_2966_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec_ref(v_as_2961_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___lam__0(lean_object* v___x_2971_, lean_object* v___x_2972_, lean_object* v___x_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_){
_start:
{
lean_object* v___x_2977_; 
v___x_2977_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___x_2971_, v___y_2974_, v___y_2975_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2997_; 
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2980_ = v___x_2977_;
v_isShared_2981_ = v_isSharedCheck_2997_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___x_2977_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2997_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2982_; uint8_t v___x_2983_; 
v___x_2982_ = lean_array_get_size(v_a_2978_);
v___x_2983_ = lean_nat_dec_lt(v___x_2972_, v___x_2982_);
if (v___x_2983_ == 0)
{
lean_object* v___x_2985_; 
lean_dec(v_a_2978_);
if (v_isShared_2981_ == 0)
{
lean_ctor_set(v___x_2980_, 0, v___x_2973_);
v___x_2985_ = v___x_2980_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___x_2973_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
else
{
uint8_t v___x_2987_; 
v___x_2987_ = lean_nat_dec_le(v___x_2982_, v___x_2982_);
if (v___x_2987_ == 0)
{
if (v___x_2983_ == 0)
{
lean_object* v___x_2989_; 
lean_dec(v_a_2978_);
if (v_isShared_2981_ == 0)
{
lean_ctor_set(v___x_2980_, 0, v___x_2973_);
v___x_2989_ = v___x_2980_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2973_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
else
{
size_t v___x_2991_; size_t v___x_2992_; lean_object* v___x_2993_; 
lean_del_object(v___x_2980_);
v___x_2991_ = ((size_t)0ULL);
v___x_2992_ = lean_usize_of_nat(v___x_2982_);
v___x_2993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1(v_a_2978_, v___x_2991_, v___x_2992_, v___x_2973_, v___y_2974_, v___y_2975_);
lean_dec(v_a_2978_);
return v___x_2993_;
}
}
else
{
size_t v___x_2994_; size_t v___x_2995_; lean_object* v___x_2996_; 
lean_del_object(v___x_2980_);
v___x_2994_ = ((size_t)0ULL);
v___x_2995_ = lean_usize_of_nat(v___x_2982_);
v___x_2996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__1(v_a_2978_, v___x_2994_, v___x_2995_, v___x_2973_, v___y_2974_, v___y_2975_);
lean_dec(v_a_2978_);
return v___x_2996_;
}
}
}
}
else
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
v_a_2998_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2977_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2977_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___lam__0___boxed(lean_object* v___x_3006_, lean_object* v___x_3007_, lean_object* v___x_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___lam__0(v___x_3006_, v___x_3007_, v___x_3008_, v___y_3009_, v___y_3010_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___x_3007_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2(lean_object* v_as_3013_, size_t v_sz_3014_, size_t v_i_3015_, lean_object* v_b_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
uint8_t v___x_3020_; 
v___x_3020_ = lean_usize_dec_lt(v_i_3015_, v_sz_3014_);
if (v___x_3020_ == 0)
{
lean_object* v___x_3021_; 
v___x_3021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3021_, 0, v_b_3016_);
return v___x_3021_;
}
else
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v_a_3024_; lean_object* v___x_3025_; lean_object* v___f_3026_; lean_object* v___x_3027_; 
v___x_3022_ = lean_unsigned_to_nat(0u);
v___x_3023_ = lean_box(0);
v_a_3024_ = lean_array_uget_borrowed(v_as_3013_, v_i_3015_);
lean_inc_n(v_a_3024_, 2);
v___x_3025_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___boxed), 8, 1);
lean_closure_set(v___x_3025_, 0, v_a_3024_);
v___f_3026_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___lam__0___boxed), 6, 3);
lean_closure_set(v___f_3026_, 0, v___x_3025_);
lean_closure_set(v___f_3026_, 1, v___x_3022_);
lean_closure_set(v___f_3026_, 2, v___x_3023_);
v___x_3027_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_a_3024_, v___f_3026_, v___y_3017_, v___y_3018_);
if (lean_obj_tag(v___x_3027_) == 0)
{
size_t v___x_3028_; size_t v___x_3029_; 
lean_dec_ref_known(v___x_3027_, 1);
v___x_3028_ = ((size_t)1ULL);
v___x_3029_ = lean_usize_add(v_i_3015_, v___x_3028_);
v_i_3015_ = v___x_3029_;
v_b_3016_ = v___x_3023_;
goto _start;
}
else
{
return v___x_3027_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2___boxed(lean_object* v_as_3031_, lean_object* v_sz_3032_, lean_object* v_i_3033_, lean_object* v_b_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
size_t v_sz_boxed_3038_; size_t v_i_boxed_3039_; lean_object* v_res_3040_; 
v_sz_boxed_3038_ = lean_unbox_usize(v_sz_3032_);
lean_dec(v_sz_3032_);
v_i_boxed_3039_ = lean_unbox_usize(v_i_3033_);
lean_dec(v_i_3033_);
v_res_3040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2(v_as_3031_, v_sz_boxed_3038_, v_i_boxed_3039_, v_b_3034_, v___y_3035_, v___y_3036_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec_ref(v_as_3031_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__3(lean_object* v_as_3041_, size_t v_i_3042_, size_t v_stop_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_){
_start:
{
uint8_t v___x_3047_; 
v___x_3047_ = lean_usize_dec_eq(v_i_3042_, v_stop_3043_);
if (v___x_3047_ == 0)
{
uint8_t v___x_3048_; uint8_t v_a_3050_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3048_ = 1;
v___x_3056_ = lean_array_uget_borrowed(v_as_3041_, v_i_3042_);
lean_inc(v___x_3056_);
v___x_3057_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__0___redArg(v___x_3056_, v___y_3045_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3067_; 
v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3060_ = v___x_3057_;
v_isShared_3061_ = v_isSharedCheck_3067_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3057_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3067_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
uint8_t v___x_3062_; 
v___x_3062_ = lean_unbox(v_a_3058_);
lean_dec(v_a_3058_);
if (v___x_3062_ == 0)
{
lean_object* v___x_3063_; lean_object* v___x_3065_; 
v___x_3063_ = lean_box(v___x_3048_);
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 0, v___x_3063_);
v___x_3065_ = v___x_3060_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___x_3063_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
else
{
lean_del_object(v___x_3060_);
v_a_3050_ = v___x_3047_;
goto v___jp_3049_;
}
}
}
else
{
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v_a_3068_; uint8_t v___x_3069_; 
v_a_3068_ = lean_ctor_get(v___x_3057_, 0);
lean_inc(v_a_3068_);
lean_dec_ref_known(v___x_3057_, 1);
v___x_3069_ = lean_unbox(v_a_3068_);
lean_dec(v_a_3068_);
v_a_3050_ = v___x_3069_;
goto v___jp_3049_;
}
else
{
return v___x_3057_;
}
}
v___jp_3049_:
{
if (v_a_3050_ == 0)
{
size_t v___x_3051_; size_t v___x_3052_; 
v___x_3051_ = ((size_t)1ULL);
v___x_3052_ = lean_usize_add(v_i_3042_, v___x_3051_);
v_i_3042_ = v___x_3052_;
goto _start;
}
else
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3054_ = lean_box(v___x_3048_);
v___x_3055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
return v___x_3055_;
}
}
}
else
{
uint8_t v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3070_ = 0;
v___x_3071_ = lean_box(v___x_3070_);
v___x_3072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
return v___x_3072_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__3___boxed(lean_object* v_as_3073_, lean_object* v_i_3074_, lean_object* v_stop_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
size_t v_i_boxed_3079_; size_t v_stop_boxed_3080_; lean_object* v_res_3081_; 
v_i_boxed_3079_ = lean_unbox_usize(v_i_3074_);
lean_dec(v_i_3074_);
v_stop_boxed_3080_ = lean_unbox_usize(v_stop_3075_);
lean_dec(v_stop_3075_);
v_res_3081_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__3(v_as_3073_, v_i_boxed_3079_, v_stop_boxed_3080_, v___y_3076_, v___y_3077_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec_ref(v_as_3073_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler(lean_object* v_declNames_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_){
_start:
{
lean_object* v___y_3110_; lean_object* v___x_3113_; lean_object* v___x_3114_; uint8_t v___x_3115_; 
v___x_3113_ = lean_unsigned_to_nat(0u);
v___x_3114_ = lean_array_get_size(v_declNames_3082_);
v___x_3115_ = lean_nat_dec_lt(v___x_3113_, v___x_3114_);
if (v___x_3115_ == 0)
{
lean_object* v___x_3116_; 
v___x_3116_ = l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0(v___x_3115_, v_a_3083_, v_a_3084_);
v___y_3110_ = v___x_3116_;
goto v___jp_3109_;
}
else
{
if (v___x_3115_ == 0)
{
goto v___jp_3086_;
}
else
{
size_t v___x_3117_; size_t v___x_3118_; lean_object* v___x_3119_; 
v___x_3117_ = ((size_t)0ULL);
v___x_3118_ = lean_usize_of_nat(v___x_3114_);
v___x_3119_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__3(v_declNames_3082_, v___x_3117_, v___x_3118_, v_a_3083_, v_a_3084_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_object* v_a_3120_; uint8_t v___x_3121_; lean_object* v___x_3122_; 
v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
lean_inc(v_a_3120_);
lean_dec_ref_known(v___x_3119_, 1);
v___x_3121_ = lean_unbox(v_a_3120_);
lean_dec(v_a_3120_);
v___x_3122_ = l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___lam__0(v___x_3121_, v_a_3083_, v_a_3084_);
v___y_3110_ = v___x_3122_;
goto v___jp_3109_;
}
else
{
v___y_3110_ = v___x_3119_;
goto v___jp_3109_;
}
}
}
v___jp_3086_:
{
lean_object* v___x_3087_; size_t v_sz_3088_; size_t v___x_3089_; lean_object* v___x_3090_; 
v___x_3087_ = lean_box(0);
v_sz_3088_ = lean_array_size(v_declNames_3082_);
v___x_3089_ = ((size_t)0ULL);
v___x_3090_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_Repr_mkReprInstanceHandler_spec__2(v_declNames_3082_, v_sz_3088_, v___x_3089_, v___x_3087_, v_a_3083_, v_a_3084_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3099_; 
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3099_ == 0)
{
lean_object* v_unused_3100_; 
v_unused_3100_ = lean_ctor_get(v___x_3090_, 0);
lean_dec(v_unused_3100_);
v___x_3092_ = v___x_3090_;
v_isShared_3093_ = v_isSharedCheck_3099_;
goto v_resetjp_3091_;
}
else
{
lean_dec(v___x_3090_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3099_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
uint8_t v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3097_; 
v___x_3094_ = 1;
v___x_3095_ = lean_box(v___x_3094_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 0, v___x_3095_);
v___x_3097_ = v___x_3092_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3095_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
else
{
lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3108_; 
v_a_3101_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3103_ = v___x_3090_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_3090_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3106_; 
if (v_isShared_3104_ == 0)
{
v___x_3106_ = v___x_3103_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_a_3101_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
v___jp_3109_:
{
if (lean_obj_tag(v___y_3110_) == 0)
{
lean_object* v_a_3111_; uint8_t v___x_3112_; 
v_a_3111_ = lean_ctor_get(v___y_3110_, 0);
v___x_3112_ = lean_unbox(v_a_3111_);
if (v___x_3112_ == 0)
{
return v___y_3110_;
}
else
{
lean_dec_ref_known(v___y_3110_, 1);
goto v___jp_3086_;
}
}
else
{
return v___y_3110_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler___boxed(lean_object* v_declNames_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_){
_start:
{
lean_object* v_res_3127_; 
v_res_3127_ = l_Lean_Elab_Deriving_Repr_mkReprInstanceHandler(v_declNames_3123_, v_a_3124_, v_a_3125_);
lean_dec(v_a_3125_);
lean_dec_ref(v_a_3124_);
lean_dec_ref(v_declNames_3123_);
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; 
v___x_3195_ = ((lean_object*)(l_Lean_Elab_Deriving_Repr_mkReprHeader___closed__1));
v___x_3196_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__0_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_));
v___x_3197_ = l_Lean_Elab_registerDerivingHandler(v___x_3195_, v___x_3196_);
if (lean_obj_tag(v___x_3197_) == 0)
{
lean_object* v___x_3198_; uint8_t v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; 
lean_dec_ref_known(v___x_3197_, 1);
v___x_3198_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_mkReprInstanceCmd___closed__0));
v___x_3199_ = 0;
v___x_3200_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn___closed__25_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_));
v___x_3201_ = l_Lean_registerTraceClass(v___x_3198_, v___x_3199_, v___x_3200_);
return v___x_3201_;
}
else
{
return v___x_3197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2____boxed(lean_object* v_a_3202_){
_start:
{
lean_object* v_res_3203_; 
v_res_3203_ = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_();
return v_res_3203_;
}
}
lean_object* runtime_initialize_Lean_Meta_Inductive(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Deriving_Repr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Inductive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Deriving_Repr_0__Lean_Elab_Deriving_Repr_initFn_00___x40_Lean_Elab_Deriving_Repr_1829928117____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Deriving_Repr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Inductive(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Deriving_Repr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Inductive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Deriving_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Deriving_Repr(builtin);
}
#ifdef __cplusplus
}
#endif
