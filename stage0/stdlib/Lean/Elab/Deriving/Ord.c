// Lean compiler output
// Module: Lean.Elab.Deriving.Ord
// Imports: public import Lean.Data.Options import Lean.Elab.Deriving.Basic import Lean.Elab.Deriving.Util import Lean.Meta.Constructions.CtorIdx import Lean.Meta.Constructions.CasesOnSameCtor import Lean.Meta.SameCtorUtils import Init.Data.Array.OfFn
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
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCIdent(lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkContext(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedInductiveVal_default;
lean_object* l_Lean_Elab_Deriving_mkHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
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
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_occursOrInType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM___redArg();
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCtorIdxName(lean_object*);
lean_object* l_Lean_mkCasesOnSameCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_mkArray3___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Elab_Deriving_mkInstanceCmds(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isInductiveCore(lean_object*, lean_object*);
lean_object* l_Lean_Elab_registerDerivingHandler(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Deriving_Ord_0__initFn_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Deriving_Ord_0__initFn_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__0_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "deriving"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__0_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__0_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__1_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ord"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__1_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__1_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__2_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "linear_construction_threshold"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__2_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__2_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__3_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__0_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(38, 127, 229, 132, 157, 42, 70, 134)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__3_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__3_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__1_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(58, 105, 173, 43, 143, 234, 178, 2)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__3_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__3_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__2_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(119, 157, 91, 192, 251, 142, 191, 166)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__3_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__3_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__4_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 350, .m_capacity = 350, .m_length = 349, .m_data = "If the inductive data type has this many or more constructors, use a different implementation for implementing `Ord` that avoids the quadratic code size produced by the default implementation.\n\nThe alternative construction compiles to less efficient code in some cases, so by default it is only used for inductive types with 10 or more constructors."};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__4_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__4_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__5_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__4_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__5_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__5_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__6_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__6_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__6_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__7_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__6_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__7_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__7_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__9_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__7_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__9_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__9_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__10_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__10_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__10_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__11_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__9_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__10_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__11_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__11_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__12_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Deriving"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__12_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__12_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__13_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__11_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__12_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(202, 58, 65, 192, 197, 114, 188, 72)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__13_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__13_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__14_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Ord"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__14_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__14_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__15_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__13_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__14_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(234, 29, 188, 163, 17, 185, 131, 241)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__15_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__15_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__16_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__15_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(235, 228, 53, 108, 241, 27, 196, 104)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__16_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__16_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__17_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__16_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__0_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(182, 7, 46, 207, 203, 113, 203, 236)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__17_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__17_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__18_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__17_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__1_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(106, 109, 90, 201, 238, 184, 42, 89)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__18_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__18_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__19_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__18_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__2_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(231, 74, 63, 253, 21, 218, 53, 222)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__19_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__19_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__deriving_ord_linear__construction__threshold;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__14_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(47, 34, 14, 190, 177, 218, 16, 31)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Ordering.then"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__4_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__5;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Ordering"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__6_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "then"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__7_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(226, 44, 125, 228, 251, 150, 72, 72)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__8_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(97, 170, 41, 107, 24, 174, 163, 92)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__8_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__9_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__8_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__10_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__11 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__11_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__9_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__11_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__12 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__12_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__13 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__13_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__15 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__15_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__16_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__16_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__16_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__15_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__16 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__16_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__17 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__17_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__17_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__19 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__19_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__20 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__20_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__20_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__21 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__21_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__22 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__22_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__24_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__10_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__24_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__12_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(230, 230, 99, 85, 138, 169, 166, 218)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__24_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__14_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(134, 215, 124, 37, 166, 123, 51, 213)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__24 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__24_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__24_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__25 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__25_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__26 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__26_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__27_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__26_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__27 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__27_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__27_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__28 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__28_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__29_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__29_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__29 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__29_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__29_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__30 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__30_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__31 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__31_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__28_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__31_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__32 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__32_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__25_value),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__32_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__33 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__33_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "compare"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__34 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__34_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__34_value),LEAN_SCALAR_PTR_LITERAL(109, 41, 149, 169, 79, 76, 232, 231)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__36 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__36_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__14_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(47, 34, 14, 190, 177, 218, 16, 31)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__37_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__34_value),LEAN_SCALAR_PTR_LITERAL(241, 180, 168, 39, 68, 69, 153, 110)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__37 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__37_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__37_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__38 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__38_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__38_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__39 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__39_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__40 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__40_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "b"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 22, 244, 233, 226, 169, 241, 142)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "inaccessible"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__4_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__5_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__5_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__5_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(243, 90, 7, 119, 108, 205, 19, 233)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__5_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ".("};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__6_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__7_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__2_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Ordering.eq"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__4_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__5;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "eq"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__6 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__6_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(226, 44, 125, 228, 251, 150, 72, 72)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__7_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__6_value),LEAN_SCALAR_PTR_LITERAL(103, 150, 86, 2, 28, 163, 164, 77)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__7 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__7_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__8 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__8_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__7_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__9 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__9_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__10 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__10_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__8_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__10_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__12 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__12_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__13_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__13_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__13_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__12_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__13 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__13_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__14 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__14_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__15 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__15_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__16;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__17 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__17_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Ordering.lt"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__18 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__18_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__19;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__20 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__20_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(226, 44, 125, 228, 251, 150, 72, 72)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__21_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__20_value),LEAN_SCALAR_PTR_LITERAL(151, 65, 236, 10, 147, 23, 177, 156)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__21 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__21_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__21_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__22 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__22_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__21_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__23 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__23_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__23_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__24 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__24_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__22_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__24_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__25 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__25_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Ordering.gt"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__26 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__26_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__27;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "gt"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__28 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__28_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(226, 44, 125, 228, 251, 150, 72, 72)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__29_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__28_value),LEAN_SCALAR_PTR_LITERAL(117, 227, 205, 91, 93, 250, 7, 4)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__29 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__29_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__29_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__30 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__30_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__29_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__31 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__31_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__31_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__32 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__32_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__30_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__32_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__33 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__33_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__5 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Term_instMonadTermElabM___lam__1___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__6 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__6___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__0_value;
static const lean_closure_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__1_value;
static const lean_array_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "match"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 208, 235, 82, 91, 230, 203, 159)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "with"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__4_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__4_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__3_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__3_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "tuple"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__5_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__5_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(191, 24, 88, 245, 200, 250, 27, 217)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Elab.Deriving.Ord"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Elab.Deriving.Ord.0.Lean.Elab.Deriving.Ord.mkMatchNew"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "assertion violation: header.targetNames.size == 2\n\n  "};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__3;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "match_on_same_ctor"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__4_value),LEAN_SCALAR_PTR_LITERAL(78, 38, 237, 47, 106, 10, 11, 248)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "matchDiscr"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__7_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__7_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__6_value),LEAN_SCALAR_PTR_LITERAL(99, 51, 127, 238, 206, 239, 57, 130)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__9;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__8_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__37_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__14 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__28_value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__14_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__15 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__25_value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__15_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__16 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__21_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__17 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__23_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__18 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__17_value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__18_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__19 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__19_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__29_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__20 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__31_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__21 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__21_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__20_value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__21_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__22 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__22_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__23 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__23_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__24 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__24_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__23_value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__24_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__25 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__25_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Nat.compare_eq_eq.mp"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__26 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__26_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__27;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__28 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__28_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "compare_eq_eq"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__29 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__29_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mp"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__30 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__30_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__28_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__31_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__29_value),LEAN_SCALAR_PTR_LITERAL(242, 151, 26, 225, 153, 203, 91, 119)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__31_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__30_value),LEAN_SCALAR_PTR_LITERAL(94, 11, 29, 173, 18, 99, 159, 69)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__31 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__31_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__28_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__32_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__29_value),LEAN_SCALAR_PTR_LITERAL(242, 151, 26, 225, 153, 203, 91, 119)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__32 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__32_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__33 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__33_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__32_value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__33_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__34 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__34_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__34_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__35 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__35_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__36 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__36_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__37;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__36_value),LEAN_SCALAR_PTR_LITERAL(77, 42, 253, 71, 61, 132, 173, 240)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__38 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__38_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__38_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__39 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__39_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__39_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__40 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__40_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__2_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__1_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__4_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__6_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__6_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__6_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__5_value),LEAN_SCALAR_PTR_LITERAL(248, 187, 217, 228, 39, 184, 218, 135)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "def"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__9_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__9_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__9_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__8_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "optDeclSig"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__11_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__11_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__11_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__10_value),LEAN_SCALAR_PTR_LITERAL(26, 9, 103, 232, 183, 57, 246, 75)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__13_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__13_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__12_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__13_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(226, 44, 125, 228, 251, 150, 72, 72)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__15 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__16 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__15_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__17 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__18 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__16_value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__18_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__19 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__19_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__20 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__21_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__21_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__21_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__20_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__21 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__21_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__22 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__22_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__23 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__23_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__24 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__24_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__25_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__25_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__23_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__25_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__24_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__25 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__25_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "partial"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__26 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__26_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__27_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__27_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__27_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__26_value),LEAN_SCALAR_PTR_LITERAL(103, 175, 198, 167, 172, 79, 14, 207)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__27 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__27_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mutual"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__0_value),LEAN_SCALAR_PTR_LITERAL(55, 205, 8, 5, 164, 77, 17, 1)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "set_option"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__2_value),LEAN_SCALAR_PTR_LITERAL(216, 223, 149, 245, 150, 86, 134, 198)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "match.ignoreUnusedAlts"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__5;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ignoreUnusedAlts"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 5, 219, 45, 43, 52, 169, 192)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__6_value),LEAN_SCALAR_PTR_LITERAL(49, 254, 67, 85, 227, 127, 91, 187)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__1_value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__8_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "end"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__12_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__0(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__10_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__12_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(195, 196, 35, 37, 101, 57, 52, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__1_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(3, 185, 255, 214, 49, 16, 173, 251)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "attribute"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__6 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__7_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__6_value),LEAN_SCALAR_PTR_LITERAL(79, 30, 18, 84, 71, 173, 185, 159)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__10_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__10_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__9_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__12_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__12_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__12_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__11_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__12 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__14 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__15_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__15_value_aux_1),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__13_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__15_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__14_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__15 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__15_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "method_specs"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__16 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__16_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__17;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__16_value),LEAN_SCALAR_PTR_LITERAL(101, 159, 225, 215, 58, 146, 25, 204)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__18 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__18_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__19 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__19_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explicitBinder"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__1_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__1_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(49, 119, 193, 23, 170, 93, 183, 238)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__3;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "y"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__5 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__6;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(72, 55, 55, 9, 143, 73, 230, 150)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__7 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__8 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__9 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__8_value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__9_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__10 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "x.ctorIdx"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__11 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__11_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__12;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ctorIdx"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__13 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(2, 247, 218, 116, 51, 159, 161, 152)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__14 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "y.ctorIdx"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__15 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__15_value;
static lean_once_cell_t l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__16;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(72, 55, 55, 9, 143, 73, 230, 150)}};
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(85, 37, 232, 186, 208, 254, 208, 112)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__17 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__17_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumCmd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumCmd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__1(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__0_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__0_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__0_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__1_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__16_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(214, 245, 77, 140, 236, 123, 248, 43)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__1_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__1_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__2_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__1_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__10_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(4, 87, 41, 84, 80, 186, 228, 139)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__2_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__2_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__3_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__2_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__12_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(214, 146, 61, 148, 52, 127, 164, 158)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__3_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__3_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__4_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__3_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__14_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(54, 226, 227, 81, 35, 13, 185, 126)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__4_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__4_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__5_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__5_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__5_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__6_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__4_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__5_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(155, 135, 205, 158, 42, 30, 240, 37)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__6_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__6_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__7_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__7_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__7_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__6_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__7_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(254, 41, 211, 152, 255, 207, 100, 126)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__9_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(199, 200, 248, 195, 255, 104, 182, 0)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__9_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__9_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__10_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__9_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__10_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(73, 190, 197, 108, 143, 88, 227, 65)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__10_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__10_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__11_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__10_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__12_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(47, 199, 3, 241, 107, 15, 45, 213)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__11_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__11_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__12_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__11_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__14_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(179, 15, 148, 183, 57, 172, 17, 87)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__12_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__12_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__13_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__12_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1187715530) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(253, 121, 178, 8, 160, 220, 233, 66)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__13_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__13_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__14_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__14_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__14_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__15_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__13_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__14_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(190, 65, 24, 154, 152, 230, 188, 253)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__15_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__15_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__16_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__16_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__16_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__17_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__15_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__16_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(50, 66, 188, 46, 171, 180, 95, 99)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__17_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__17_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__18_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__17_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(11, 83, 81, 67, 51, 241, 247, 37)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__18_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__18_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Deriving_Ord_0__initFn_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
lean_inc(v_defValue_5_);
v___x_8_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_8_, 0, v_defValue_5_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_9_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_9_, 0, v_name_1_);
lean_ctor_set(v___x_9_, 1, v_ref_3_);
lean_ctor_set(v___x_9_, 2, v___x_8_);
lean_ctor_set(v___x_9_, 3, v_descr_6_);
lean_ctor_set(v___x_9_, 4, v_deprecation_x3f_7_);
v___x_10_ = lean_register_option(v_name_1_, v___x_9_);
if (lean_obj_tag(v___x_10_) == 0)
{
lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_18_; 
v_isSharedCheck_18_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_18_ == 0)
{
lean_object* v_unused_19_; 
v_unused_19_ = lean_ctor_get(v___x_10_, 0);
lean_dec(v_unused_19_);
v___x_12_ = v___x_10_;
v_isShared_13_ = v_isSharedCheck_18_;
goto v_resetjp_11_;
}
else
{
lean_dec(v___x_10_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_18_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v___x_14_; lean_object* v___x_16_; 
lean_inc(v_defValue_5_);
v___x_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_14_, 0, v_name_1_);
lean_ctor_set(v___x_14_, 1, v_defValue_5_);
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 0, v___x_14_);
v___x_16_ = v___x_12_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v___x_14_);
v___x_16_ = v_reuseFailAlloc_17_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
return v___x_16_;
}
}
}
else
{
lean_object* v_a_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_27_; 
lean_dec(v_name_1_);
v_a_20_ = lean_ctor_get(v___x_10_, 0);
v_isSharedCheck_27_ = !lean_is_exclusive(v___x_10_);
if (v_isSharedCheck_27_ == 0)
{
v___x_22_ = v___x_10_;
v_isShared_23_ = v_isSharedCheck_27_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_a_20_);
lean_dec(v___x_10_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_27_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_25_; 
if (v_isShared_23_ == 0)
{
v___x_25_ = v___x_22_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v_a_20_);
v___x_25_ = v_reuseFailAlloc_26_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
return v___x_25_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_Deriving_Ord_0__initFn_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_28_, lean_object* v_decl_29_, lean_object* v_ref_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Option_register___at___00__private_Lean_Elab_Deriving_Ord_0__initFn_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__spec__0(v_name_28_, v_decl_29_, v_ref_30_);
lean_dec_ref(v_decl_29_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_78_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__3_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_));
v___x_79_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__5_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_));
v___x_80_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__19_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_));
v___x_81_ = l_Lean_Option_register___at___00__private_Lean_Elab_Deriving_Ord_0__initFn_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__spec__0(v___x_78_, v___x_79_, v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__initFn_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4____boxed(lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l___private_Lean_Elab_Deriving_Ord_0__initFn_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_();
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader(lean_object* v_indVal_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader___closed__0));
v___x_95_ = lean_unsigned_to_nat(2u);
v___x_96_ = l_Lean_Elab_Deriving_mkHeader(v___x_94_, v___x_95_, v_indVal_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader___boxed(lean_object* v_indVal_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader(v_indVal_97_, v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
lean_dec(v_a_101_);
lean_dec_ref(v_a_100_);
lean_dec(v_a_99_);
lean_dec_ref(v_a_98_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg___lam__0(lean_object* v_k_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v_b_109_, lean_object* v_c_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_){
_start:
{
lean_object* v___x_116_; 
lean_inc(v___y_114_);
lean_inc_ref(v___y_113_);
lean_inc(v___y_112_);
lean_inc_ref(v___y_111_);
lean_inc(v___y_108_);
lean_inc_ref(v___y_107_);
v___x_116_ = lean_apply_9(v_k_106_, v_b_109_, v_c_110_, v___y_107_, v___y_108_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, lean_box(0));
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg___lam__0___boxed(lean_object* v_k_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v_b_120_, lean_object* v_c_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg___lam__0(v_k_117_, v___y_118_, v___y_119_, v_b_120_, v_c_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg(lean_object* v_type_128_, lean_object* v_k_129_, uint8_t v_cleanupAnnotations_130_, uint8_t v_whnfType_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v___f_139_; lean_object* v___x_140_; 
lean_inc(v___y_133_);
lean_inc_ref(v___y_132_);
v___f_139_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_139_, 0, v_k_129_);
lean_closure_set(v___f_139_, 1, v___y_132_);
lean_closure_set(v___f_139_, 2, v___y_133_);
v___x_140_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_128_, v___f_139_, v_cleanupAnnotations_130_, v_whnfType_131_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
if (lean_obj_tag(v___x_140_) == 0)
{
return v___x_140_;
}
else
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_148_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_148_ == 0)
{
v___x_143_ = v___x_140_;
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_140_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_a_141_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg___boxed(lean_object* v_type_149_, lean_object* v_k_150_, lean_object* v_cleanupAnnotations_151_, lean_object* v_whnfType_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_160_; uint8_t v_whnfType_boxed_161_; lean_object* v_res_162_; 
v_cleanupAnnotations_boxed_160_ = lean_unbox(v_cleanupAnnotations_151_);
v_whnfType_boxed_161_ = lean_unbox(v_whnfType_152_);
v_res_162_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg(v_type_149_, v_k_150_, v_cleanupAnnotations_boxed_160_, v_whnfType_boxed_161_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5(lean_object* v_00_u03b1_163_, lean_object* v_type_164_, lean_object* v_k_165_, uint8_t v_cleanupAnnotations_166_, uint8_t v_whnfType_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg(v_type_164_, v_k_165_, v_cleanupAnnotations_166_, v_whnfType_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___boxed(lean_object* v_00_u03b1_176_, lean_object* v_type_177_, lean_object* v_k_178_, lean_object* v_cleanupAnnotations_179_, lean_object* v_whnfType_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_188_; uint8_t v_whnfType_boxed_189_; lean_object* v_res_190_; 
v_cleanupAnnotations_boxed_188_ = lean_unbox(v_cleanupAnnotations_179_);
v_whnfType_boxed_189_ = lean_unbox(v_whnfType_180_);
v_res_190_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5(v_00_u03b1_176_, v_type_177_, v_k_178_, v_cleanupAnnotations_boxed_188_, v_whnfType_boxed_189_, v___y_181_, v___y_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
lean_dec(v___y_184_);
lean_dec_ref(v___y_183_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__1(size_t v_sz_191_, size_t v_i_192_, lean_object* v_bs_193_){
_start:
{
uint8_t v___x_194_; 
v___x_194_ = lean_usize_dec_lt(v_i_192_, v_sz_191_);
if (v___x_194_ == 0)
{
return v_bs_193_;
}
else
{
lean_object* v_v_195_; lean_object* v___x_196_; lean_object* v_bs_x27_197_; size_t v___x_198_; size_t v___x_199_; lean_object* v___x_200_; 
v_v_195_ = lean_array_uget(v_bs_193_, v_i_192_);
v___x_196_ = lean_unsigned_to_nat(0u);
v_bs_x27_197_ = lean_array_uset(v_bs_193_, v_i_192_, v___x_196_);
v___x_198_ = ((size_t)1ULL);
v___x_199_ = lean_usize_add(v_i_192_, v___x_198_);
v___x_200_ = lean_array_uset(v_bs_x27_197_, v_i_192_, v_v_195_);
v_i_192_ = v___x_199_;
v_bs_193_ = v___x_200_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__1___boxed(lean_object* v_sz_202_, lean_object* v_i_203_, lean_object* v_bs_204_){
_start:
{
size_t v_sz_boxed_205_; size_t v_i_boxed_206_; lean_object* v_res_207_; 
v_sz_boxed_205_ = lean_unbox_usize(v_sz_202_);
lean_dec(v_sz_202_);
v_i_boxed_206_ = lean_unbox_usize(v_i_203_);
lean_dec(v_i_203_);
v_res_207_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__1(v_sz_boxed_205_, v_i_boxed_206_, v_bs_204_);
return v_res_207_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__4));
v___x_218_ = l_String_toRawSubstring_x27(v___x_217_);
return v___x_218_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__22));
v___x_256_ = l_String_toRawSubstring_x27(v___x_255_);
return v___x_256_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__34));
v___x_287_ = l_String_toRawSubstring_x27(v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0(uint8_t v___x_300_, lean_object* v___x_301_, lean_object* v___x_302_, lean_object* v_snd_303_, lean_object* v_rhs_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_toCold_312_; lean_object* v_ref_313_; lean_object* v_quotContext_314_; lean_object* v_currMacroScope_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_toCold_312_ = lean_ctor_get(v___y_309_, 0);
v_ref_313_ = lean_ctor_get(v___y_309_, 2);
v_quotContext_314_ = lean_ctor_get(v_toCold_312_, 8);
v_currMacroScope_315_ = lean_ctor_get(v_toCold_312_, 9);
v___x_316_ = l_Lean_SourceInfo_fromRef(v_ref_313_, v___x_300_);
v___x_317_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3));
v___x_318_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__5);
v___x_319_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__8));
lean_inc_n(v_currMacroScope_315_, 3);
lean_inc_n(v_quotContext_314_, 3);
v___x_320_ = l_Lean_addMacroScope(v_quotContext_314_, v___x_319_, v_currMacroScope_315_);
v___x_321_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__12));
lean_inc_n(v___x_316_, 11);
v___x_322_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_322_, 0, v___x_316_);
lean_ctor_set(v___x_322_, 1, v___x_318_);
lean_ctor_set(v___x_322_, 2, v___x_320_);
lean_ctor_set(v___x_322_, 3, v___x_321_);
v___x_323_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_324_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__16));
v___x_325_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18));
v___x_326_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__19));
v___x_327_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_316_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
v___x_328_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__21));
v___x_329_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23);
v___x_330_ = lean_box(0);
v___x_331_ = l_Lean_addMacroScope(v_quotContext_314_, v___x_330_, v_currMacroScope_315_);
v___x_332_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__33));
v___x_333_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_333_, 0, v___x_316_);
lean_ctor_set(v___x_333_, 1, v___x_329_);
lean_ctor_set(v___x_333_, 2, v___x_331_);
lean_ctor_set(v___x_333_, 3, v___x_332_);
v___x_334_ = l_Lean_Syntax_node1(v___x_316_, v___x_328_, v___x_333_);
v___x_335_ = l_Lean_Syntax_node2(v___x_316_, v___x_325_, v___x_327_, v___x_334_);
v___x_336_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35);
v___x_337_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__36));
v___x_338_ = l_Lean_addMacroScope(v_quotContext_314_, v___x_337_, v_currMacroScope_315_);
v___x_339_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__39));
v___x_340_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_340_, 0, v___x_316_);
lean_ctor_set(v___x_340_, 1, v___x_336_);
lean_ctor_set(v___x_340_, 2, v___x_338_);
lean_ctor_set(v___x_340_, 3, v___x_339_);
v___x_341_ = l_Lean_Syntax_node2(v___x_316_, v___x_323_, v___x_301_, v___x_302_);
v___x_342_ = l_Lean_Syntax_node2(v___x_316_, v___x_317_, v___x_340_, v___x_341_);
v___x_343_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__40));
v___x_344_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_316_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = l_Lean_Syntax_node3(v___x_316_, v___x_324_, v___x_335_, v___x_342_, v___x_344_);
v___x_346_ = l_Lean_Syntax_node2(v___x_316_, v___x_323_, v___x_345_, v_rhs_304_);
v___x_347_ = l_Lean_Syntax_node2(v___x_316_, v___x_317_, v___x_322_, v___x_346_);
lean_inc(v___y_310_);
lean_inc_ref(v___y_309_);
lean_inc(v___y_308_);
lean_inc_ref(v___y_307_);
lean_inc(v___y_306_);
lean_inc_ref(v___y_305_);
v___x_348_ = lean_apply_8(v_snd_303_, v___x_347_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, lean_box(0));
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___boxed(lean_object* v___x_349_, lean_object* v___x_350_, lean_object* v___x_351_, lean_object* v_snd_352_, lean_object* v_rhs_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
uint8_t v___x_49197__boxed_361_; lean_object* v_res_362_; 
v___x_49197__boxed_361_ = lean_unbox(v___x_349_);
v_res_362_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0(v___x_49197__boxed_361_, v___x_350_, v___x_351_, v_snd_352_, v_rhs_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg(lean_object* v_upperBound_383_, lean_object* v___x_384_, lean_object* v_xs_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_b_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_a_395_; uint8_t v___x_399_; 
v___x_399_ = lean_nat_dec_lt(v_a_387_, v_upperBound_383_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; 
lean_dec(v_a_387_);
v___x_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_400_, 0, v_b_388_);
return v___x_400_;
}
else
{
lean_object* v_snd_401_; lean_object* v_fst_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_506_; 
v_snd_401_ = lean_ctor_get(v_b_388_, 1);
v_fst_402_ = lean_ctor_get(v_b_388_, 0);
v_isSharedCheck_506_ = !lean_is_exclusive(v_b_388_);
if (v_isSharedCheck_506_ == 0)
{
v___x_404_ = v_b_388_;
v_isShared_405_ = v_isSharedCheck_506_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_snd_401_);
lean_inc(v_fst_402_);
lean_dec(v_b_388_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_506_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v_fst_406_; lean_object* v_snd_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_505_; 
v_fst_406_ = lean_ctor_get(v_snd_401_, 0);
v_snd_407_ = lean_ctor_get(v_snd_401_, 1);
v_isSharedCheck_505_ = !lean_is_exclusive(v_snd_401_);
if (v_isSharedCheck_505_ == 0)
{
v___x_409_ = v_snd_401_;
v_isShared_410_ = v_isSharedCheck_505_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_snd_407_);
lean_inc(v_fst_406_);
lean_dec(v_snd_401_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_505_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_411_ = l_Lean_instInhabitedExpr;
v___x_412_ = lean_nat_add(v___x_384_, v_a_387_);
v___x_413_ = lean_array_get_borrowed(v___x_411_, v_xs_385_, v___x_412_);
lean_dec(v___x_412_);
lean_inc(v___x_413_);
v___x_414_ = l_Lean_Meta_isProof(v___x_413_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
if (lean_obj_tag(v___x_414_) == 0)
{
lean_object* v_a_415_; uint8_t v___x_416_; 
v_a_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_a_415_);
lean_dec_ref_known(v___x_414_, 1);
v___x_416_ = lean_unbox(v_a_415_);
if (v___x_416_ == 0)
{
lean_object* v_lctx_417_; uint8_t v___x_418_; 
v_lctx_417_ = lean_ctor_get(v___y_389_, 2);
lean_inc(v___x_413_);
lean_inc_ref(v_lctx_417_);
v___x_418_ = l_Lean_Meta_occursOrInType(v_lctx_417_, v___x_413_, v_a_386_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; lean_object* v___x_420_; 
lean_dec(v_a_415_);
v___x_419_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__1));
v___x_420_ = l_Lean_Core_mkFreshUserName(v___x_419_, v___y_391_, v___y_392_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_a_421_);
lean_dec_ref_known(v___x_420_, 1);
v___x_422_ = l_Lean_mkIdent(v_a_421_);
v___x_423_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__3));
v___x_424_ = l_Lean_Core_mkFreshUserName(v___x_423_, v___y_391_, v___y_392_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___f_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_432_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_a_425_);
lean_dec_ref_known(v___x_424_, 1);
v___x_426_ = l_Lean_mkIdent(v_a_425_);
v___x_427_ = lean_box(v___x_418_);
lean_inc(v___x_426_);
lean_inc(v___x_422_);
v___f_428_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_428_, 0, v___x_427_);
lean_closure_set(v___f_428_, 1, v___x_422_);
lean_closure_set(v___f_428_, 2, v___x_426_);
lean_closure_set(v___f_428_, 3, v_snd_407_);
v___x_429_ = lean_array_push(v_fst_402_, v___x_422_);
v___x_430_ = lean_array_push(v_fst_406_, v___x_426_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 1, v___f_428_);
lean_ctor_set(v___x_409_, 0, v___x_430_);
v___x_432_ = v___x_409_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_430_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v___f_428_);
v___x_432_ = v_reuseFailAlloc_436_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_434_; 
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 1, v___x_432_);
lean_ctor_set(v___x_404_, 0, v___x_429_);
v___x_434_ = v___x_404_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_429_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v___x_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
v_a_395_ = v___x_434_;
goto v___jp_394_;
}
}
}
else
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
lean_dec(v___x_422_);
lean_del_object(v___x_409_);
lean_dec(v_snd_407_);
lean_dec(v_fst_406_);
lean_del_object(v___x_404_);
lean_dec(v_fst_402_);
lean_dec(v_a_387_);
v_a_437_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v___x_424_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_424_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
else
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
lean_del_object(v___x_409_);
lean_dec(v_snd_407_);
lean_dec(v_fst_406_);
lean_del_object(v___x_404_);
lean_dec(v_fst_402_);
lean_dec(v_a_387_);
v_a_445_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_452_ == 0)
{
v___x_447_ = v___x_420_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_420_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_a_445_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
else
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__1));
v___x_454_ = l_Lean_Core_mkFreshUserName(v___x_453_, v___y_391_, v___y_392_);
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v_a_455_; lean_object* v_ref_456_; lean_object* v___x_457_; lean_object* v___x_458_; uint8_t v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_469_; 
v_a_455_ = lean_ctor_get(v___x_454_, 0);
lean_inc(v_a_455_);
lean_dec_ref_known(v___x_454_, 1);
v_ref_456_ = lean_ctor_get(v___y_391_, 2);
v___x_457_ = l_Lean_mkIdent(v_a_455_);
lean_inc(v___x_457_);
v___x_458_ = lean_array_push(v_fst_402_, v___x_457_);
v___x_459_ = lean_unbox(v_a_415_);
lean_dec(v_a_415_);
v___x_460_ = l_Lean_SourceInfo_fromRef(v_ref_456_, v___x_459_);
v___x_461_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__5));
v___x_462_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__6));
lean_inc_n(v___x_460_, 2);
v___x_463_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_460_);
lean_ctor_set(v___x_463_, 1, v___x_462_);
v___x_464_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__40));
v___x_465_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_460_);
lean_ctor_set(v___x_465_, 1, v___x_464_);
v___x_466_ = l_Lean_Syntax_node3(v___x_460_, v___x_461_, v___x_463_, v___x_457_, v___x_465_);
v___x_467_ = lean_array_push(v_fst_406_, v___x_466_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_467_);
v___x_469_ = v___x_409_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_snd_407_);
v___x_469_ = v_reuseFailAlloc_473_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_471_; 
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 1, v___x_469_);
lean_ctor_set(v___x_404_, 0, v___x_458_);
v___x_471_ = v___x_404_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_458_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v___x_469_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
v_a_395_ = v___x_471_;
goto v___jp_394_;
}
}
}
else
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
lean_dec(v_a_415_);
lean_del_object(v___x_409_);
lean_dec(v_snd_407_);
lean_dec(v_fst_406_);
lean_del_object(v___x_404_);
lean_dec(v_fst_402_);
lean_dec(v_a_387_);
v_a_474_ = lean_ctor_get(v___x_454_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_454_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_454_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_474_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
else
{
lean_object* v_ref_482_; uint8_t v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_492_; 
lean_dec(v_a_415_);
v_ref_482_ = lean_ctor_get(v___y_391_, 2);
v___x_483_ = 0;
v___x_484_ = l_Lean_SourceInfo_fromRef(v_ref_482_, v___x_483_);
v___x_485_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8));
v___x_486_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__9));
lean_inc(v___x_484_);
v___x_487_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_484_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = l_Lean_Syntax_node1(v___x_484_, v___x_485_, v___x_487_);
lean_inc(v___x_488_);
v___x_489_ = lean_array_push(v_fst_402_, v___x_488_);
v___x_490_ = lean_array_push(v_fst_406_, v___x_488_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_490_);
v___x_492_ = v___x_409_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_snd_407_);
v___x_492_ = v_reuseFailAlloc_496_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_494_; 
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 1, v___x_492_);
lean_ctor_set(v___x_404_, 0, v___x_489_);
v___x_494_ = v___x_404_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_489_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v___x_492_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
v_a_395_ = v___x_494_;
goto v___jp_394_;
}
}
}
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_del_object(v___x_409_);
lean_dec(v_snd_407_);
lean_dec(v_fst_406_);
lean_del_object(v___x_404_);
lean_dec(v_fst_402_);
lean_dec(v_a_387_);
v_a_497_ = lean_ctor_get(v___x_414_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_414_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_414_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
}
v___jp_394_:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = lean_unsigned_to_nat(1u);
v___x_397_ = lean_nat_add(v_a_387_, v___x_396_);
lean_dec(v_a_387_);
v_a_387_ = v___x_397_;
v_b_388_ = v_a_395_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___boxed(lean_object* v_upperBound_507_, lean_object* v___x_508_, lean_object* v_xs_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_b_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg(v_upperBound_507_, v___x_508_, v_xs_509_, v_a_510_, v_a_511_, v_b_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec_ref(v_a_510_);
lean_dec_ref(v_xs_509_);
lean_dec(v___x_508_);
lean_dec(v_upperBound_507_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4___redArg(lean_object* v_upperBound_519_, lean_object* v_a_520_, lean_object* v_b_521_, lean_object* v___y_522_){
_start:
{
uint8_t v___x_524_; 
v___x_524_ = lean_nat_dec_lt(v_a_520_, v_upperBound_519_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; 
lean_dec(v_a_520_);
v___x_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_525_, 0, v_b_521_);
return v___x_525_;
}
else
{
lean_object* v_ref_526_; uint8_t v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v_ref_526_ = lean_ctor_get(v___y_522_, 2);
v___x_527_ = 0;
v___x_528_ = l_Lean_SourceInfo_fromRef(v_ref_526_, v___x_527_);
v___x_529_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8));
v___x_530_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__9));
lean_inc(v___x_528_);
v___x_531_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_528_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = l_Lean_Syntax_node1(v___x_528_, v___x_529_, v___x_531_);
v___x_533_ = lean_array_push(v_b_521_, v___x_532_);
v___x_534_ = lean_unsigned_to_nat(1u);
v___x_535_ = lean_nat_add(v_a_520_, v___x_534_);
lean_dec(v_a_520_);
v_a_520_ = v___x_535_;
v_b_521_ = v___x_533_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4___redArg___boxed(lean_object* v_upperBound_537_, lean_object* v_a_538_, lean_object* v_b_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4___redArg(v_upperBound_537_, v_a_538_, v_b_539_, v___y_540_);
lean_dec_ref(v___y_540_);
lean_dec(v_upperBound_537_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3___redArg(lean_object* v_upperBound_543_, lean_object* v_a_544_, lean_object* v_b_545_, lean_object* v___y_546_){
_start:
{
uint8_t v___x_548_; 
v___x_548_ = lean_nat_dec_lt(v_a_544_, v_upperBound_543_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; 
lean_dec(v_a_544_);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v_b_545_);
return v___x_549_;
}
else
{
lean_object* v_fst_550_; lean_object* v_snd_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_570_; 
v_fst_550_ = lean_ctor_get(v_b_545_, 0);
v_snd_551_ = lean_ctor_get(v_b_545_, 1);
v_isSharedCheck_570_ = !lean_is_exclusive(v_b_545_);
if (v_isSharedCheck_570_ == 0)
{
v___x_553_ = v_b_545_;
v_isShared_554_ = v_isSharedCheck_570_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_snd_551_);
lean_inc(v_fst_550_);
lean_dec(v_b_545_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_570_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v_ref_555_; uint8_t v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_565_; 
v_ref_555_ = lean_ctor_get(v___y_546_, 2);
v___x_556_ = 0;
v___x_557_ = l_Lean_SourceInfo_fromRef(v_ref_555_, v___x_556_);
v___x_558_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8));
v___x_559_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__9));
lean_inc(v___x_557_);
v___x_560_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_557_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
v___x_561_ = l_Lean_Syntax_node1(v___x_557_, v___x_558_, v___x_560_);
lean_inc(v___x_561_);
v___x_562_ = lean_array_push(v_fst_550_, v___x_561_);
v___x_563_ = lean_array_push(v_snd_551_, v___x_561_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 1, v___x_563_);
lean_ctor_set(v___x_553_, 0, v___x_562_);
v___x_565_ = v___x_553_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v___x_563_);
v___x_565_ = v_reuseFailAlloc_569_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_unsigned_to_nat(1u);
v___x_567_ = lean_nat_add(v_a_544_, v___x_566_);
lean_dec(v_a_544_);
v_a_544_ = v___x_567_;
v_b_545_ = v___x_565_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3___redArg___boxed(lean_object* v_upperBound_571_, lean_object* v_a_572_, lean_object* v_b_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3___redArg(v_upperBound_571_, v_a_572_, v_b_573_, v___y_574_);
lean_dec_ref(v___y_574_);
lean_dec(v_upperBound_571_);
return v_res_576_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3(void){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Array_mkArray0___redArg();
return v___x_584_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__4));
v___x_587_ = l_String_toRawSubstring_x27(v___x_586_);
return v___x_587_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__16(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__15));
v___x_612_ = l_Lean_mkAtom(v___x_611_);
return v___x_612_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__19(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_615_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__18));
v___x_616_ = l_String_toRawSubstring_x27(v___x_615_);
return v___x_616_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__27(void){
_start:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__26));
v___x_634_ = l_String_toRawSubstring_x27(v___x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2(lean_object* v_indVal_650_, lean_object* v___x_651_, lean_object* v_alts_652_, lean_object* v___f_653_, lean_object* v_numFields_654_, lean_object* v_head_655_, lean_object* v___f_656_, lean_object* v_xs_657_, lean_object* v_type_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_Core_betaReduce(v_type_658_, v___y_663_, v___y_664_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v_numParams_668_; lean_object* v_numIndices_669_; lean_object* v___x_670_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
lean_dec_ref_known(v___x_666_, 1);
v_numParams_668_ = lean_ctor_get(v_indVal_650_, 1);
v_numIndices_669_ = lean_ctor_get(v_indVal_650_, 2);
lean_inc_ref(v_alts_652_);
lean_inc(v___x_651_);
v___x_670_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4___redArg(v_numIndices_669_, v___x_651_, v_alts_652_, v___y_663_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_671_);
lean_dec_ref_known(v___x_670_, 1);
lean_inc_ref(v_alts_652_);
v___x_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_672_, 0, v_alts_652_);
lean_ctor_set(v___x_672_, 1, v_alts_652_);
lean_inc(v___x_651_);
v___x_673_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3___redArg(v_numParams_668_, v___x_651_, v___x_672_, v___y_663_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v_fst_675_; lean_object* v_snd_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_887_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_a_674_);
lean_dec_ref_known(v___x_673_, 1);
v_fst_675_ = lean_ctor_get(v_a_674_, 0);
v_snd_676_ = lean_ctor_get(v_a_674_, 1);
v_isSharedCheck_887_ = !lean_is_exclusive(v_a_674_);
if (v_isSharedCheck_887_ == 0)
{
v___x_678_ = v_a_674_;
v_isShared_679_ = v_isSharedCheck_887_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_snd_676_);
lean_inc(v_fst_675_);
lean_dec(v_a_674_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_887_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 1, v___f_653_);
lean_ctor_set(v___x_678_, 0, v_snd_676_);
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_snd_676_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v___f_653_);
v___x_681_ = v_reuseFailAlloc_886_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_682_, 0, v_fst_675_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg(v_numFields_654_, v_numParams_668_, v_xs_657_, v_a_667_, v___x_651_, v___x_682_, v___y_661_, v___y_662_, v___y_663_, v___y_664_);
lean_dec(v_a_667_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v_snd_685_; lean_object* v_fst_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_877_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_a_684_);
lean_dec_ref_known(v___x_683_, 1);
v_snd_685_ = lean_ctor_get(v_a_684_, 1);
v_fst_686_ = lean_ctor_get(v_a_684_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v_a_684_);
if (v_isSharedCheck_877_ == 0)
{
v___x_688_ = v_a_684_;
v_isShared_689_ = v_isSharedCheck_877_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_snd_685_);
lean_inc(v_fst_686_);
lean_dec(v_a_684_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_877_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_fst_690_; lean_object* v_snd_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_876_; 
v_fst_690_ = lean_ctor_get(v_snd_685_, 0);
v_snd_691_ = lean_ctor_get(v_snd_685_, 1);
v_isSharedCheck_876_ = !lean_is_exclusive(v_snd_685_);
if (v_isSharedCheck_876_ == 0)
{
v___x_693_ = v_snd_685_;
v_isShared_694_ = v_isSharedCheck_876_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_snd_691_);
lean_inc(v_fst_690_);
lean_dec(v_snd_685_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_876_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v_toCold_695_; lean_object* v_ref_696_; uint8_t v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
v_toCold_695_ = lean_ctor_get(v___y_663_, 0);
v_ref_696_ = lean_ctor_get(v___y_663_, 2);
v___x_697_ = 0;
v___x_698_ = l_Lean_SourceInfo_fromRef(v_ref_696_, v___x_697_);
v___x_699_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3));
v___x_700_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1));
v___x_701_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__2));
lean_inc(v___x_698_);
if (v_isShared_694_ == 0)
{
lean_ctor_set_tag(v___x_693_, 2);
lean_ctor_set(v___x_693_, 1, v___x_701_);
lean_ctor_set(v___x_693_, 0, v___x_698_);
v___x_703_ = v___x_693_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v___x_701_);
v___x_703_ = v_reuseFailAlloc_875_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_704_ = l_Lean_mkIdent(v_head_655_);
lean_inc(v___x_704_);
lean_inc_n(v___x_698_, 2);
v___x_705_ = l_Lean_Syntax_node2(v___x_698_, v___x_700_, v___x_703_, v___x_704_);
v___x_706_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_707_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3);
v___x_708_ = l_Array_append___redArg(v___x_707_, v_fst_686_);
lean_dec(v_fst_686_);
v___x_709_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_709_, 0, v___x_698_);
lean_ctor_set(v___x_709_, 1, v___x_706_);
lean_ctor_set(v___x_709_, 2, v___x_708_);
v___x_710_ = l_Lean_Syntax_node2(v___x_698_, v___x_699_, v___x_705_, v___x_709_);
lean_inc_ref(v___f_656_);
lean_inc(v___y_664_);
lean_inc_ref(v___y_663_);
lean_inc(v___y_662_);
lean_inc_ref(v___y_661_);
lean_inc(v___y_660_);
lean_inc_ref(v___y_659_);
v___x_711_ = lean_apply_7(v___f_656_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, lean_box(0));
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v___x_714_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc_n(v_a_712_, 2);
lean_dec_ref_known(v___x_711_, 1);
if (v_isShared_689_ == 0)
{
lean_ctor_set_tag(v___x_688_, 2);
lean_ctor_set(v___x_688_, 1, v___x_701_);
lean_ctor_set(v___x_688_, 0, v_a_712_);
v___x_714_ = v___x_688_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_712_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v___x_701_);
v___x_714_ = v_reuseFailAlloc_866_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
lean_inc_n(v_a_712_, 2);
v___x_715_ = l_Lean_Syntax_node2(v_a_712_, v___x_700_, v___x_714_, v___x_704_);
v___x_716_ = l_Array_append___redArg(v___x_707_, v_fst_690_);
lean_dec(v_fst_690_);
v___x_717_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_717_, 0, v_a_712_);
lean_ctor_set(v___x_717_, 1, v___x_706_);
lean_ctor_set(v___x_717_, 2, v___x_716_);
v___x_718_ = l_Lean_Syntax_node2(v_a_712_, v___x_699_, v___x_715_, v___x_717_);
v___x_719_ = lean_unsigned_to_nat(2u);
v___x_720_ = lean_mk_empty_array_with_capacity(v___x_719_);
lean_inc(v___x_710_);
lean_inc_ref(v___x_720_);
v___x_721_ = lean_array_push(v___x_720_, v___x_710_);
lean_inc_ref(v___x_721_);
v___x_722_ = lean_array_push(v___x_721_, v___x_718_);
lean_inc(v_a_671_);
v___x_723_ = l_Array_append___redArg(v_a_671_, v___x_722_);
lean_dec_ref(v___x_722_);
lean_inc_ref(v___f_656_);
lean_inc(v___y_664_);
lean_inc_ref(v___y_663_);
lean_inc(v___y_662_);
lean_inc_ref(v___y_661_);
lean_inc(v___y_660_);
lean_inc_ref(v___y_659_);
v___x_724_ = lean_apply_7(v___f_656_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, lean_box(0));
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc_n(v_a_725_, 2);
lean_dec_ref_known(v___x_724_, 1);
v___x_726_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8));
v___x_727_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__9));
v___x_728_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_728_, 0, v_a_725_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
v___x_729_ = l_Lean_Syntax_node1(v_a_725_, v___x_726_, v___x_728_);
v___x_730_ = lean_array_push(v___x_721_, v___x_729_);
lean_inc(v_a_671_);
v___x_731_ = l_Array_append___redArg(v_a_671_, v___x_730_);
lean_dec_ref(v___x_730_);
lean_inc_ref(v___f_656_);
lean_inc(v___y_664_);
lean_inc_ref(v___y_663_);
lean_inc(v___y_662_);
lean_inc_ref(v___y_661_);
lean_inc(v___y_660_);
lean_inc_ref(v___y_659_);
v___x_732_ = lean_apply_7(v___f_656_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, lean_box(0));
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc_n(v_a_733_, 2);
lean_dec_ref_known(v___x_732_, 1);
v___x_734_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_734_, 0, v_a_733_);
lean_ctor_set(v___x_734_, 1, v___x_727_);
v___x_735_ = l_Lean_Syntax_node1(v_a_733_, v___x_726_, v___x_734_);
v___x_736_ = lean_array_push(v___x_720_, v___x_735_);
v___x_737_ = lean_array_push(v___x_736_, v___x_710_);
v___x_738_ = l_Array_append___redArg(v_a_671_, v___x_737_);
lean_dec_ref(v___x_737_);
lean_inc_ref(v___f_656_);
lean_inc(v___y_664_);
lean_inc_ref(v___y_663_);
lean_inc(v___y_662_);
lean_inc_ref(v___y_661_);
lean_inc(v___y_660_);
lean_inc_ref(v___y_659_);
v___x_739_ = lean_apply_7(v___f_656_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, lean_box(0));
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v_quotContext_741_; lean_object* v_currMacroScope_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_a_740_);
lean_dec_ref_known(v___x_739_, 1);
v_quotContext_741_ = lean_ctor_get(v_toCold_695_, 8);
v_currMacroScope_742_ = lean_ctor_get(v_toCold_695_, 9);
v___x_743_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__5);
v___x_744_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__7));
lean_inc(v_currMacroScope_742_);
lean_inc(v_quotContext_741_);
v___x_745_ = l_Lean_addMacroScope(v_quotContext_741_, v___x_744_, v_currMacroScope_742_);
v___x_746_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11));
v___x_747_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_747_, 0, v_a_740_);
lean_ctor_set(v___x_747_, 1, v___x_743_);
lean_ctor_set(v___x_747_, 2, v___x_745_);
lean_ctor_set(v___x_747_, 3, v___x_746_);
lean_inc(v___y_664_);
lean_inc_ref(v___y_663_);
lean_inc(v___y_662_);
lean_inc_ref(v___y_661_);
lean_inc(v___y_660_);
lean_inc_ref(v___y_659_);
v___x_748_ = lean_apply_8(v_snd_691_, v___x_747_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, lean_box(0));
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_a_749_; lean_object* v___x_750_; 
v_a_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_a_749_);
lean_dec_ref_known(v___x_748_, 1);
lean_inc_ref(v___f_656_);
lean_inc(v___y_664_);
lean_inc_ref(v___y_663_);
lean_inc(v___y_662_);
lean_inc_ref(v___y_661_);
lean_inc(v___y_660_);
lean_inc_ref(v___y_659_);
v___x_750_ = lean_apply_7(v___f_656_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, lean_box(0));
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; size_t v_sz_755_; size_t v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc_n(v_a_751_, 5);
lean_dec_ref_known(v___x_750_, 1);
v___x_752_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__13));
v___x_753_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__14));
v___x_754_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_754_, 0, v_a_751_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
v_sz_755_ = lean_array_size(v___x_723_);
v___x_756_ = ((size_t)0ULL);
v___x_757_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__1(v_sz_755_, v___x_756_, v___x_723_);
v___x_758_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__16, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__16_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__16);
v___x_759_ = l_Lean_mkSepArray(v___x_757_, v___x_758_);
lean_dec_ref(v___x_757_);
v___x_760_ = l_Array_append___redArg(v___x_707_, v___x_759_);
lean_dec_ref(v___x_759_);
v___x_761_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_761_, 0, v_a_751_);
lean_ctor_set(v___x_761_, 1, v___x_706_);
lean_ctor_set(v___x_761_, 2, v___x_760_);
v___x_762_ = l_Lean_Syntax_node1(v_a_751_, v___x_706_, v___x_761_);
v___x_763_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__17));
v___x_764_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_764_, 0, v_a_751_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___x_765_ = l_Lean_Syntax_node4(v_a_751_, v___x_752_, v___x_754_, v___x_762_, v___x_764_, v_a_749_);
lean_inc_ref(v___f_656_);
lean_inc(v___y_664_);
lean_inc_ref(v___y_663_);
lean_inc(v___y_662_);
lean_inc_ref(v___y_661_);
lean_inc(v___y_660_);
lean_inc_ref(v___y_659_);
v___x_766_ = lean_apply_7(v___f_656_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, lean_box(0));
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_768_; size_t v_sz_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc_n(v_a_767_, 6);
lean_dec_ref_known(v___x_766_, 1);
v___x_768_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_768_, 0, v_a_767_);
lean_ctor_set(v___x_768_, 1, v___x_753_);
v_sz_769_ = lean_array_size(v___x_731_);
v___x_770_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__1(v_sz_769_, v___x_756_, v___x_731_);
v___x_771_ = l_Lean_mkSepArray(v___x_770_, v___x_758_);
lean_dec_ref(v___x_770_);
v___x_772_ = l_Array_append___redArg(v___x_707_, v___x_771_);
lean_dec_ref(v___x_771_);
v___x_773_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_773_, 0, v_a_767_);
lean_ctor_set(v___x_773_, 1, v___x_706_);
lean_ctor_set(v___x_773_, 2, v___x_772_);
v___x_774_ = l_Lean_Syntax_node1(v_a_767_, v___x_706_, v___x_773_);
v___x_775_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_775_, 0, v_a_767_);
lean_ctor_set(v___x_775_, 1, v___x_763_);
v___x_776_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__19, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__19_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__19);
v___x_777_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__21));
lean_inc(v_currMacroScope_742_);
lean_inc(v_quotContext_741_);
v___x_778_ = l_Lean_addMacroScope(v_quotContext_741_, v___x_777_, v_currMacroScope_742_);
v___x_779_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__25));
v___x_780_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_780_, 0, v_a_767_);
lean_ctor_set(v___x_780_, 1, v___x_776_);
lean_ctor_set(v___x_780_, 2, v___x_778_);
lean_ctor_set(v___x_780_, 3, v___x_779_);
v___x_781_ = l_Lean_Syntax_node4(v_a_767_, v___x_752_, v___x_768_, v___x_774_, v___x_775_, v___x_780_);
lean_inc(v___y_664_);
lean_inc_ref(v___y_663_);
lean_inc(v___y_662_);
lean_inc_ref(v___y_661_);
lean_inc(v___y_660_);
lean_inc_ref(v___y_659_);
v___x_782_ = lean_apply_7(v___f_656_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, lean_box(0));
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_809_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_809_ == 0)
{
v___x_785_ = v___x_782_;
v_isShared_786_ = v_isSharedCheck_809_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_782_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_809_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_787_; size_t v_sz_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_807_; 
lean_inc_n(v_a_783_, 5);
v___x_787_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_787_, 0, v_a_783_);
lean_ctor_set(v___x_787_, 1, v___x_753_);
v_sz_788_ = lean_array_size(v___x_738_);
v___x_789_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__1(v_sz_788_, v___x_756_, v___x_738_);
v___x_790_ = l_Lean_mkSepArray(v___x_789_, v___x_758_);
lean_dec_ref(v___x_789_);
v___x_791_ = l_Array_append___redArg(v___x_707_, v___x_790_);
lean_dec_ref(v___x_790_);
v___x_792_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_792_, 0, v_a_783_);
lean_ctor_set(v___x_792_, 1, v___x_706_);
lean_ctor_set(v___x_792_, 2, v___x_791_);
v___x_793_ = l_Lean_Syntax_node1(v_a_783_, v___x_706_, v___x_792_);
v___x_794_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_794_, 0, v_a_783_);
lean_ctor_set(v___x_794_, 1, v___x_763_);
v___x_795_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__27, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__27_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__27);
v___x_796_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__29));
lean_inc(v_currMacroScope_742_);
lean_inc(v_quotContext_741_);
v___x_797_ = l_Lean_addMacroScope(v_quotContext_741_, v___x_796_, v_currMacroScope_742_);
v___x_798_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__33));
v___x_799_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_799_, 0, v_a_783_);
lean_ctor_set(v___x_799_, 1, v___x_795_);
lean_ctor_set(v___x_799_, 2, v___x_797_);
lean_ctor_set(v___x_799_, 3, v___x_798_);
v___x_800_ = l_Lean_Syntax_node4(v_a_783_, v___x_752_, v___x_787_, v___x_793_, v___x_794_, v___x_799_);
v___x_801_ = lean_unsigned_to_nat(3u);
v___x_802_ = lean_mk_empty_array_with_capacity(v___x_801_);
v___x_803_ = lean_array_push(v___x_802_, v___x_765_);
v___x_804_ = lean_array_push(v___x_803_, v___x_781_);
v___x_805_ = lean_array_push(v___x_804_, v___x_800_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 0, v___x_805_);
v___x_807_ = v___x_785_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_805_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec(v___x_781_);
lean_dec(v___x_765_);
lean_dec_ref(v___x_738_);
v_a_810_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_782_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_782_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
lean_dec(v___x_765_);
lean_dec_ref(v___x_738_);
lean_dec_ref(v___x_731_);
lean_dec_ref(v___f_656_);
v_a_818_ = lean_ctor_get(v___x_766_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_766_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_766_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_766_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
lean_dec(v_a_749_);
lean_dec_ref(v___x_738_);
lean_dec_ref(v___x_731_);
lean_dec_ref(v___x_723_);
lean_dec_ref(v___f_656_);
v_a_826_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_750_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_750_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
else
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_841_; 
lean_dec_ref(v___x_738_);
lean_dec_ref(v___x_731_);
lean_dec_ref(v___x_723_);
lean_dec_ref(v___f_656_);
v_a_834_ = lean_ctor_get(v___x_748_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_748_);
if (v_isSharedCheck_841_ == 0)
{
v___x_836_ = v___x_748_;
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_748_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_841_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_a_834_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
else
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec_ref(v___x_738_);
lean_dec_ref(v___x_731_);
lean_dec_ref(v___x_723_);
lean_dec(v_snd_691_);
lean_dec_ref(v___f_656_);
v_a_842_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_739_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_739_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
lean_dec_ref(v___x_731_);
lean_dec_ref(v___x_723_);
lean_dec_ref(v___x_720_);
lean_dec(v___x_710_);
lean_dec(v_snd_691_);
lean_dec(v_a_671_);
lean_dec_ref(v___f_656_);
v_a_850_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_732_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_732_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec_ref(v___x_723_);
lean_dec_ref(v___x_721_);
lean_dec_ref(v___x_720_);
lean_dec(v___x_710_);
lean_dec(v_snd_691_);
lean_dec(v_a_671_);
lean_dec_ref(v___f_656_);
v_a_858_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_724_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_724_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
}
else
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
lean_dec(v___x_710_);
lean_dec(v___x_704_);
lean_dec(v_snd_691_);
lean_dec(v_fst_690_);
lean_del_object(v___x_688_);
lean_dec(v_a_671_);
lean_dec_ref(v___f_656_);
v_a_867_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_711_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_711_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
lean_dec(v_a_671_);
lean_dec_ref(v___f_656_);
lean_dec(v_head_655_);
v_a_878_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_683_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_683_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
}
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec(v_a_671_);
lean_dec(v_a_667_);
lean_dec_ref(v___f_656_);
lean_dec(v_head_655_);
lean_dec_ref(v___f_653_);
lean_dec(v___x_651_);
v_a_888_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_673_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_673_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
else
{
lean_dec(v_a_667_);
lean_dec_ref(v___f_656_);
lean_dec(v_head_655_);
lean_dec_ref(v___f_653_);
lean_dec_ref(v_alts_652_);
lean_dec(v___x_651_);
return v___x_670_;
}
}
else
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
lean_dec_ref(v___f_656_);
lean_dec(v_head_655_);
lean_dec_ref(v___f_653_);
lean_dec_ref(v_alts_652_);
lean_dec(v___x_651_);
v_a_896_ = lean_ctor_get(v___x_666_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_666_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_666_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___boxed(lean_object* v_indVal_904_, lean_object* v___x_905_, lean_object* v_alts_906_, lean_object* v___f_907_, lean_object* v_numFields_908_, lean_object* v_head_909_, lean_object* v___f_910_, lean_object* v_xs_911_, lean_object* v_type_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2(v_indVal_904_, v___x_905_, v_alts_906_, v___f_907_, v_numFields_908_, v_head_909_, v___f_910_, v_xs_911_, v_type_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec_ref(v_xs_911_);
lean_dec(v_numFields_908_);
lean_dec_ref(v_indVal_904_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__1(lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_ref_928_; uint8_t v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v_ref_928_ = lean_ctor_get(v___y_925_, 2);
v___x_929_ = 0;
v___x_930_ = l_Lean_SourceInfo_fromRef(v_ref_928_, v___x_929_);
v___x_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__1___boxed(lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__1(v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__0(lean_object* v_rhs_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_948_, 0, v_rhs_940_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__0___boxed(lean_object* v_rhs_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__0(v_rhs_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
return v_res_957_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_instMonadEIO___redArg();
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1(lean_object* v_msg_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v_toApplicative_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_1066_; 
v___x_973_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__0);
v___x_974_ = l_StateRefT_x27_instMonad___redArg(v___x_973_);
v_toApplicative_975_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_1066_ == 0)
{
lean_object* v_unused_1067_; 
v_unused_1067_ = lean_ctor_get(v___x_974_, 1);
lean_dec(v_unused_1067_);
v___x_977_ = v___x_974_;
v_isShared_978_ = v_isSharedCheck_1066_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_toApplicative_975_);
lean_dec(v___x_974_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_1066_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v_toFunctor_979_; lean_object* v_toSeq_980_; lean_object* v_toSeqLeft_981_; lean_object* v_toSeqRight_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_1064_; 
v_toFunctor_979_ = lean_ctor_get(v_toApplicative_975_, 0);
v_toSeq_980_ = lean_ctor_get(v_toApplicative_975_, 2);
v_toSeqLeft_981_ = lean_ctor_get(v_toApplicative_975_, 3);
v_toSeqRight_982_ = lean_ctor_get(v_toApplicative_975_, 4);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_toApplicative_975_);
if (v_isSharedCheck_1064_ == 0)
{
lean_object* v_unused_1065_; 
v_unused_1065_ = lean_ctor_get(v_toApplicative_975_, 1);
lean_dec(v_unused_1065_);
v___x_984_ = v_toApplicative_975_;
v_isShared_985_ = v_isSharedCheck_1064_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_toSeqRight_982_);
lean_inc(v_toSeqLeft_981_);
lean_inc(v_toSeq_980_);
lean_inc(v_toFunctor_979_);
lean_dec(v_toApplicative_975_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_1064_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___f_986_; lean_object* v___f_987_; lean_object* v___f_988_; lean_object* v___f_989_; lean_object* v___x_990_; lean_object* v___f_991_; lean_object* v___f_992_; lean_object* v___f_993_; lean_object* v___x_995_; 
v___f_986_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__1));
v___f_987_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__2));
lean_inc_ref(v_toFunctor_979_);
v___f_988_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_988_, 0, v_toFunctor_979_);
v___f_989_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_989_, 0, v_toFunctor_979_);
v___x_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_990_, 0, v___f_988_);
lean_ctor_set(v___x_990_, 1, v___f_989_);
v___f_991_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_991_, 0, v_toSeqRight_982_);
v___f_992_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_992_, 0, v_toSeqLeft_981_);
v___f_993_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_993_, 0, v_toSeq_980_);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 4, v___f_991_);
lean_ctor_set(v___x_984_, 3, v___f_992_);
lean_ctor_set(v___x_984_, 2, v___f_993_);
lean_ctor_set(v___x_984_, 1, v___f_986_);
lean_ctor_set(v___x_984_, 0, v___x_990_);
v___x_995_ = v___x_984_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_990_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v___f_986_);
lean_ctor_set(v_reuseFailAlloc_1063_, 2, v___f_993_);
lean_ctor_set(v_reuseFailAlloc_1063_, 3, v___f_992_);
lean_ctor_set(v_reuseFailAlloc_1063_, 4, v___f_991_);
v___x_995_ = v_reuseFailAlloc_1063_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
lean_object* v___x_997_; 
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 1, v___f_987_);
lean_ctor_set(v___x_977_, 0, v___x_995_);
v___x_997_ = v___x_977_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v___f_987_);
v___x_997_ = v_reuseFailAlloc_1062_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
lean_object* v___x_998_; lean_object* v_toApplicative_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1060_; 
v___x_998_ = l_StateRefT_x27_instMonad___redArg(v___x_997_);
v_toApplicative_999_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1060_ == 0)
{
lean_object* v_unused_1061_; 
v_unused_1061_ = lean_ctor_get(v___x_998_, 1);
lean_dec(v_unused_1061_);
v___x_1001_ = v___x_998_;
v_isShared_1002_ = v_isSharedCheck_1060_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_toApplicative_999_);
lean_dec(v___x_998_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1060_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v_toFunctor_1003_; lean_object* v_toSeq_1004_; lean_object* v_toSeqLeft_1005_; lean_object* v_toSeqRight_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1058_; 
v_toFunctor_1003_ = lean_ctor_get(v_toApplicative_999_, 0);
v_toSeq_1004_ = lean_ctor_get(v_toApplicative_999_, 2);
v_toSeqLeft_1005_ = lean_ctor_get(v_toApplicative_999_, 3);
v_toSeqRight_1006_ = lean_ctor_get(v_toApplicative_999_, 4);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_toApplicative_999_);
if (v_isSharedCheck_1058_ == 0)
{
lean_object* v_unused_1059_; 
v_unused_1059_ = lean_ctor_get(v_toApplicative_999_, 1);
lean_dec(v_unused_1059_);
v___x_1008_ = v_toApplicative_999_;
v_isShared_1009_ = v_isSharedCheck_1058_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_toSeqRight_1006_);
lean_inc(v_toSeqLeft_1005_);
lean_inc(v_toSeq_1004_);
lean_inc(v_toFunctor_1003_);
lean_dec(v_toApplicative_999_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1058_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___f_1010_; lean_object* v___f_1011_; lean_object* v___f_1012_; lean_object* v___f_1013_; lean_object* v___x_1014_; lean_object* v___f_1015_; lean_object* v___f_1016_; lean_object* v___f_1017_; lean_object* v___x_1019_; 
v___f_1010_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__3));
v___f_1011_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1003_);
v___f_1012_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1012_, 0, v_toFunctor_1003_);
v___f_1013_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1013_, 0, v_toFunctor_1003_);
v___x_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___f_1012_);
lean_ctor_set(v___x_1014_, 1, v___f_1013_);
v___f_1015_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1015_, 0, v_toSeqRight_1006_);
v___f_1016_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1016_, 0, v_toSeqLeft_1005_);
v___f_1017_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1017_, 0, v_toSeq_1004_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 4, v___f_1015_);
lean_ctor_set(v___x_1008_, 3, v___f_1016_);
lean_ctor_set(v___x_1008_, 2, v___f_1017_);
lean_ctor_set(v___x_1008_, 1, v___f_1010_);
lean_ctor_set(v___x_1008_, 0, v___x_1014_);
v___x_1019_ = v___x_1008_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1014_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v___f_1010_);
lean_ctor_set(v_reuseFailAlloc_1057_, 2, v___f_1017_);
lean_ctor_set(v_reuseFailAlloc_1057_, 3, v___f_1016_);
lean_ctor_set(v_reuseFailAlloc_1057_, 4, v___f_1015_);
v___x_1019_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
lean_object* v___x_1021_; 
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 1, v___f_1011_);
lean_ctor_set(v___x_1001_, 0, v___x_1019_);
v___x_1021_ = v___x_1001_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1019_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v___f_1011_);
v___x_1021_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
lean_object* v___x_1022_; lean_object* v_toApplicative_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1054_; 
v___x_1022_ = l_StateRefT_x27_instMonad___redArg(v___x_1021_);
v_toApplicative_1023_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1054_ == 0)
{
lean_object* v_unused_1055_; 
v_unused_1055_ = lean_ctor_get(v___x_1022_, 1);
lean_dec(v_unused_1055_);
v___x_1025_ = v___x_1022_;
v_isShared_1026_ = v_isSharedCheck_1054_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_toApplicative_1023_);
lean_dec(v___x_1022_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1054_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v_toFunctor_1027_; lean_object* v_toSeq_1028_; lean_object* v_toSeqLeft_1029_; lean_object* v_toSeqRight_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1052_; 
v_toFunctor_1027_ = lean_ctor_get(v_toApplicative_1023_, 0);
v_toSeq_1028_ = lean_ctor_get(v_toApplicative_1023_, 2);
v_toSeqLeft_1029_ = lean_ctor_get(v_toApplicative_1023_, 3);
v_toSeqRight_1030_ = lean_ctor_get(v_toApplicative_1023_, 4);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_toApplicative_1023_);
if (v_isSharedCheck_1052_ == 0)
{
lean_object* v_unused_1053_; 
v_unused_1053_ = lean_ctor_get(v_toApplicative_1023_, 1);
lean_dec(v_unused_1053_);
v___x_1032_ = v_toApplicative_1023_;
v_isShared_1033_ = v_isSharedCheck_1052_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_toSeqRight_1030_);
lean_inc(v_toSeqLeft_1029_);
lean_inc(v_toSeq_1028_);
lean_inc(v_toFunctor_1027_);
lean_dec(v_toApplicative_1023_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1052_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___f_1034_; lean_object* v___f_1035_; lean_object* v___f_1036_; lean_object* v___f_1037_; lean_object* v___x_1038_; lean_object* v___f_1039_; lean_object* v___f_1040_; lean_object* v___f_1041_; lean_object* v___x_1043_; 
v___f_1034_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__5));
v___f_1035_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__6));
lean_inc_ref(v_toFunctor_1027_);
v___f_1036_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1036_, 0, v_toFunctor_1027_);
v___f_1037_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1037_, 0, v_toFunctor_1027_);
v___x_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___f_1036_);
lean_ctor_set(v___x_1038_, 1, v___f_1037_);
v___f_1039_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1039_, 0, v_toSeqRight_1030_);
v___f_1040_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1040_, 0, v_toSeqLeft_1029_);
v___f_1041_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1041_, 0, v_toSeq_1028_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 4, v___f_1039_);
lean_ctor_set(v___x_1032_, 3, v___f_1040_);
lean_ctor_set(v___x_1032_, 2, v___f_1041_);
lean_ctor_set(v___x_1032_, 1, v___f_1034_);
lean_ctor_set(v___x_1032_, 0, v___x_1038_);
v___x_1043_ = v___x_1032_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v___f_1034_);
lean_ctor_set(v_reuseFailAlloc_1051_, 2, v___f_1041_);
lean_ctor_set(v_reuseFailAlloc_1051_, 3, v___f_1040_);
lean_ctor_set(v_reuseFailAlloc_1051_, 4, v___f_1039_);
v___x_1043_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
lean_object* v___x_1045_; 
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 1, v___f_1035_);
lean_ctor_set(v___x_1025_, 0, v___x_1043_);
v___x_1045_ = v___x_1025_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v___f_1035_);
v___x_1045_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_46436__overap_1048_; lean_object* v___x_1049_; 
v___x_1046_ = lean_box(0);
v___x_1047_ = l_instInhabitedOfMonad___redArg(v___x_1045_, v___x_1046_);
v___x_46436__overap_1048_ = lean_panic_fn_borrowed(v___x_1047_, v_msg_965_);
lean_dec(v___x_1047_);
lean_inc(v___y_971_);
lean_inc_ref(v___y_970_);
lean_inc(v___y_969_);
lean_inc_ref(v___y_968_);
lean_inc(v___y_967_);
lean_inc_ref(v___y_966_);
v___x_1049_ = lean_apply_7(v___x_46436__overap_1048_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, lean_box(0));
return v___x_1049_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___boxed(lean_object* v_msg_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1(v_msg_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(lean_object* v_msgData_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v___x_1083_; lean_object* v_env_1084_; lean_object* v___x_1085_; lean_object* v_toCold_1086_; lean_object* v_mctx_1087_; lean_object* v_lctx_1088_; lean_object* v_options_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1083_ = lean_st_ref_get(v___y_1081_);
v_env_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc_ref(v_env_1084_);
lean_dec(v___x_1083_);
v___x_1085_ = lean_st_ref_get(v___y_1079_);
v_toCold_1086_ = lean_ctor_get(v___y_1080_, 0);
v_mctx_1087_ = lean_ctor_get(v___x_1085_, 0);
lean_inc_ref(v_mctx_1087_);
lean_dec(v___x_1085_);
v_lctx_1088_ = lean_ctor_get(v___y_1078_, 2);
v_options_1089_ = lean_ctor_get(v_toCold_1086_, 2);
lean_inc_ref(v_options_1089_);
lean_inc_ref(v_lctx_1088_);
v___x_1090_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1090_, 0, v_env_1084_);
lean_ctor_set(v___x_1090_, 1, v_mctx_1087_);
lean_ctor_set(v___x_1090_, 2, v_lctx_1088_);
lean_ctor_set(v___x_1090_, 3, v_options_1089_);
v___x_1091_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
lean_ctor_set(v___x_1091_, 1, v_msgData_1077_);
v___x_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1091_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(v_msgData_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
return v_res_1099_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = lean_box(1);
v___x_1101_ = l_Lean_MessageData_ofFormat(v___x_1100_);
return v___x_1101_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__2));
v___x_1106_ = l_Lean_MessageData_ofFormat(v___x_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12(lean_object* v_x_1107_, lean_object* v_x_1108_){
_start:
{
if (lean_obj_tag(v_x_1108_) == 0)
{
return v_x_1107_;
}
else
{
lean_object* v_head_1109_; lean_object* v_tail_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1132_; 
v_head_1109_ = lean_ctor_get(v_x_1108_, 0);
v_tail_1110_ = lean_ctor_get(v_x_1108_, 1);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_x_1108_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1112_ = v_x_1108_;
v_isShared_1113_ = v_isSharedCheck_1132_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_tail_1110_);
lean_inc(v_head_1109_);
lean_dec(v_x_1108_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1132_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v_before_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1130_; 
v_before_1114_ = lean_ctor_get(v_head_1109_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_head_1109_);
if (v_isSharedCheck_1130_ == 0)
{
lean_object* v_unused_1131_; 
v_unused_1131_ = lean_ctor_get(v_head_1109_, 1);
lean_dec(v_unused_1131_);
v___x_1116_ = v_head_1109_;
v_isShared_1117_ = v_isSharedCheck_1130_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_before_1114_);
lean_dec(v_head_1109_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1130_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1118_; lean_object* v___x_1120_; 
v___x_1118_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0);
if (v_isShared_1117_ == 0)
{
lean_ctor_set_tag(v___x_1116_, 7);
lean_ctor_set(v___x_1116_, 1, v___x_1118_);
lean_ctor_set(v___x_1116_, 0, v_x_1107_);
v___x_1120_ = v___x_1116_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_x_1107_);
lean_ctor_set(v_reuseFailAlloc_1129_, 1, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
lean_object* v___x_1121_; lean_object* v___x_1123_; 
v___x_1121_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3);
if (v_isShared_1113_ == 0)
{
lean_ctor_set_tag(v___x_1112_, 7);
lean_ctor_set(v___x_1112_, 1, v___x_1121_);
lean_ctor_set(v___x_1112_, 0, v___x_1120_);
v___x_1123_ = v___x_1112_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1120_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v___x_1121_);
v___x_1123_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1124_ = l_Lean_MessageData_ofSyntax(v_before_1114_);
v___x_1125_ = l_Lean_indentD(v___x_1124_);
v___x_1126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1123_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v_x_1107_ = v___x_1126_;
v_x_1108_ = v_tail_1110_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(lean_object* v_opts_1133_, lean_object* v_opt_1134_){
_start:
{
lean_object* v_name_1135_; lean_object* v_defValue_1136_; lean_object* v_map_1137_; lean_object* v___x_1138_; 
v_name_1135_ = lean_ctor_get(v_opt_1134_, 0);
v_defValue_1136_ = lean_ctor_get(v_opt_1134_, 1);
v_map_1137_ = lean_ctor_get(v_opts_1133_, 0);
v___x_1138_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1137_, v_name_1135_);
if (lean_obj_tag(v___x_1138_) == 0)
{
uint8_t v___x_1139_; 
v___x_1139_ = lean_unbox(v_defValue_1136_);
return v___x_1139_;
}
else
{
lean_object* v_val_1140_; 
v_val_1140_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_val_1140_);
lean_dec_ref_known(v___x_1138_, 1);
if (lean_obj_tag(v_val_1140_) == 1)
{
uint8_t v_v_1141_; 
v_v_1141_ = lean_ctor_get_uint8(v_val_1140_, 0);
lean_dec_ref_known(v_val_1140_, 0);
return v_v_1141_;
}
else
{
uint8_t v___x_1142_; 
lean_dec(v_val_1140_);
v___x_1142_ = lean_unbox(v_defValue_1136_);
return v___x_1142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___boxed(lean_object* v_opts_1143_, lean_object* v_opt_1144_){
_start:
{
uint8_t v_res_1145_; lean_object* v_r_1146_; 
v_res_1145_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(v_opts_1143_, v_opt_1144_);
lean_dec_ref(v_opt_1144_);
lean_dec_ref(v_opts_1143_);
v_r_1146_ = lean_box(v_res_1145_);
return v_r_1146_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1));
v___x_1151_ = l_Lean_MessageData_ofFormat(v___x_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(lean_object* v_msgData_1152_, lean_object* v_macroStack_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_toCold_1156_; lean_object* v_options_1157_; lean_object* v___x_1158_; uint8_t v___x_1159_; 
v_toCold_1156_ = lean_ctor_get(v___y_1154_, 0);
v_options_1157_ = lean_ctor_get(v_toCold_1156_, 2);
v___x_1158_ = l_Lean_Elab_pp_macroStack;
v___x_1159_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(v_options_1157_, v___x_1158_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; 
lean_dec(v_macroStack_1153_);
v___x_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1160_, 0, v_msgData_1152_);
return v___x_1160_;
}
else
{
if (lean_obj_tag(v_macroStack_1153_) == 0)
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1161_, 0, v_msgData_1152_);
return v___x_1161_;
}
else
{
lean_object* v_head_1162_; lean_object* v_after_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1178_; 
v_head_1162_ = lean_ctor_get(v_macroStack_1153_, 0);
lean_inc(v_head_1162_);
v_after_1163_ = lean_ctor_get(v_head_1162_, 1);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_head_1162_);
if (v_isSharedCheck_1178_ == 0)
{
lean_object* v_unused_1179_; 
v_unused_1179_ = lean_ctor_get(v_head_1162_, 0);
lean_dec(v_unused_1179_);
v___x_1165_ = v_head_1162_;
v_isShared_1166_ = v_isSharedCheck_1178_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_after_1163_);
lean_dec(v_head_1162_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1178_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1167_; lean_object* v___x_1169_; 
v___x_1167_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0);
if (v_isShared_1166_ == 0)
{
lean_ctor_set_tag(v___x_1165_, 7);
lean_ctor_set(v___x_1165_, 1, v___x_1167_);
lean_ctor_set(v___x_1165_, 0, v_msgData_1152_);
v___x_1169_ = v___x_1165_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_msgData_1152_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v___x_1167_);
v___x_1169_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v_msgData_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1170_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_1171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1169_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
v___x_1172_ = l_Lean_MessageData_ofSyntax(v_after_1163_);
v___x_1173_ = l_Lean_indentD(v___x_1172_);
v_msgData_1174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1174_, 0, v___x_1171_);
lean_ctor_set(v_msgData_1174_, 1, v___x_1173_);
v___x_1175_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12(v_msgData_1174_, v_macroStack_1153_);
v___x_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
return v___x_1176_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_msgData_1180_, lean_object* v_macroStack_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(v_msgData_1180_, v_macroStack_1181_, v___y_1182_);
lean_dec_ref(v___y_1182_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0___redArg(lean_object* v_msg_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v_ref_1193_; lean_object* v_macroStack_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v_a_1197_; lean_object* v___x_1198_; lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1207_; 
v_ref_1193_ = lean_ctor_get(v___y_1190_, 2);
v_macroStack_1194_ = lean_ctor_get(v___y_1186_, 1);
v___x_1195_ = l_Lean_Elab_getBetterRef(v_ref_1193_, v_macroStack_1194_);
v___x_1196_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(v_msg_1185_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_a_1197_);
lean_dec_ref(v___x_1196_);
lean_inc(v_macroStack_1194_);
v___x_1198_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(v_a_1197_, v_macroStack_1194_, v___y_1190_);
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1201_ = v___x_1198_;
v_isShared_1202_ = v_isSharedCheck_1207_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1198_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1207_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1195_);
lean_ctor_set(v___x_1203_, 1, v_a_1199_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set_tag(v___x_1201_, 1);
lean_ctor_set(v___x_1201_, 0, v___x_1203_);
v___x_1205_ = v___x_1201_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0___redArg(v_msg_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
return v_res_1216_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__0));
v___x_1219_ = l_Lean_stringToMessageData(v___x_1218_);
return v___x_1219_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__2));
v___x_1222_ = l_Lean_stringToMessageData(v___x_1221_);
return v___x_1222_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__7(void){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1226_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__6));
v___x_1227_ = lean_unsigned_to_nat(11u);
v___x_1228_ = lean_unsigned_to_nat(122u);
v___x_1229_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__5));
v___x_1230_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__4));
v___x_1231_ = l_mkPanicMessageWithDecl(v___x_1230_, v___x_1229_, v___x_1228_, v___x_1227_, v___x_1226_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0(lean_object* v_constName_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v___x_1248_; lean_object* v_env_1249_; uint8_t v___x_1250_; lean_object* v___x_1251_; 
v___x_1248_ = lean_st_ref_get(v___y_1238_);
v_env_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc_ref(v_env_1249_);
lean_dec(v___x_1248_);
v___x_1250_ = 0;
lean_inc(v_constName_1232_);
v___x_1251_ = l_Lean_Environment_findAsync_x3f(v_env_1249_, v_constName_1232_, v___x_1250_);
if (lean_obj_tag(v___x_1251_) == 1)
{
lean_object* v_val_1252_; uint8_t v_kind_1253_; 
v_val_1252_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_val_1252_);
lean_dec_ref_known(v___x_1251_, 1);
v_kind_1253_ = lean_ctor_get_uint8(v_val_1252_, sizeof(void*)*3);
if (v_kind_1253_ == 6)
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1252_);
if (lean_obj_tag(v___x_1254_) == 6)
{
lean_object* v_val_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1262_; 
lean_dec(v_constName_1232_);
v_val_1255_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1257_ = v___x_1254_;
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_val_1255_);
lean_dec(v___x_1254_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set_tag(v___x_1257_, 0);
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_val_1255_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
else
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
lean_dec_ref(v___x_1254_);
v___x_1263_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__7);
v___x_1264_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1(v___x_1263_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
if (lean_obj_tag(v___x_1264_) == 0)
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1273_; 
v_a_1265_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1267_ = v___x_1264_;
v_isShared_1268_ = v_isSharedCheck_1273_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1264_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1273_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
if (lean_obj_tag(v_a_1265_) == 0)
{
lean_del_object(v___x_1267_);
goto v___jp_1240_;
}
else
{
lean_object* v_val_1269_; lean_object* v___x_1271_; 
lean_dec(v_constName_1232_);
v_val_1269_ = lean_ctor_get(v_a_1265_, 0);
lean_inc(v_val_1269_);
lean_dec_ref_known(v_a_1265_, 1);
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 0, v_val_1269_);
v___x_1271_ = v___x_1267_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_val_1269_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
lean_dec(v_constName_1232_);
v_a_1274_ = lean_ctor_get(v___x_1264_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1264_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1264_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
}
else
{
lean_dec(v_val_1252_);
goto v___jp_1240_;
}
}
else
{
lean_dec(v___x_1251_);
goto v___jp_1240_;
}
v___jp_1240_:
{
lean_object* v___x_1241_; uint8_t v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1241_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1);
v___x_1242_ = 0;
v___x_1243_ = l_Lean_MessageData_ofConstName(v_constName_1232_, v___x_1242_);
v___x_1244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1241_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
v___x_1245_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__3);
v___x_1246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1244_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v___x_1247_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0___redArg(v___x_1246_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
return v___x_1247_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___boxed(lean_object* v_constName_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0(v_constName_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__6(size_t v_sz_1291_, size_t v_i_1292_, lean_object* v_bs_1293_){
_start:
{
uint8_t v___x_1294_; 
v___x_1294_ = lean_usize_dec_lt(v_i_1292_, v_sz_1291_);
if (v___x_1294_ == 0)
{
return v_bs_1293_;
}
else
{
lean_object* v_v_1295_; lean_object* v___x_1296_; lean_object* v_bs_x27_1297_; size_t v___x_1298_; size_t v___x_1299_; lean_object* v___x_1300_; 
v_v_1295_ = lean_array_uget(v_bs_1293_, v_i_1292_);
v___x_1296_ = lean_unsigned_to_nat(0u);
v_bs_x27_1297_ = lean_array_uset(v_bs_1293_, v_i_1292_, v___x_1296_);
v___x_1298_ = ((size_t)1ULL);
v___x_1299_ = lean_usize_add(v_i_1292_, v___x_1298_);
v___x_1300_ = lean_array_uset(v_bs_x27_1297_, v_i_1292_, v_v_1295_);
v_i_1292_ = v___x_1299_;
v_bs_1293_ = v___x_1300_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__6___boxed(lean_object* v_sz_1302_, lean_object* v_i_1303_, lean_object* v_bs_1304_){
_start:
{
size_t v_sz_boxed_1305_; size_t v_i_boxed_1306_; lean_object* v_res_1307_; 
v_sz_boxed_1305_ = lean_unbox_usize(v_sz_1302_);
lean_dec(v_sz_1302_);
v_i_boxed_1306_ = lean_unbox_usize(v_i_1303_);
lean_dec(v_i_1303_);
v_res_1307_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__6(v_sz_boxed_1305_, v_i_boxed_1306_, v_bs_1304_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg(lean_object* v_indVal_1312_, lean_object* v_as_x27_1313_, lean_object* v_b_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
if (lean_obj_tag(v_as_x27_1313_) == 0)
{
lean_object* v___x_1322_; 
lean_dec_ref(v_indVal_1312_);
v___x_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1322_, 0, v_b_1314_);
return v___x_1322_;
}
else
{
lean_object* v_head_1323_; lean_object* v_tail_1324_; lean_object* v___f_1325_; lean_object* v___f_1326_; lean_object* v___x_1327_; lean_object* v_alts_1328_; lean_object* v___x_1329_; 
v_head_1323_ = lean_ctor_get(v_as_x27_1313_, 0);
v_tail_1324_ = lean_ctor_get(v_as_x27_1313_, 1);
v___f_1325_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__0));
v___f_1326_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__1));
v___x_1327_ = lean_unsigned_to_nat(0u);
v_alts_1328_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__2));
lean_inc(v_head_1323_);
v___x_1329_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0(v_head_1323_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v_toConstantVal_1331_; lean_object* v_numFields_1332_; lean_object* v_type_1333_; lean_object* v___f_1334_; uint8_t v___x_1335_; lean_object* v___x_1336_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_a_1330_);
lean_dec_ref_known(v___x_1329_, 1);
v_toConstantVal_1331_ = lean_ctor_get(v_a_1330_, 0);
lean_inc_ref(v_toConstantVal_1331_);
v_numFields_1332_ = lean_ctor_get(v_a_1330_, 4);
lean_inc(v_numFields_1332_);
lean_dec(v_a_1330_);
v_type_1333_ = lean_ctor_get(v_toConstantVal_1331_, 2);
lean_inc_ref(v_type_1333_);
lean_dec_ref(v_toConstantVal_1331_);
lean_inc(v_head_1323_);
lean_inc_ref(v_indVal_1312_);
v___f_1334_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___boxed), 16, 7);
lean_closure_set(v___f_1334_, 0, v_indVal_1312_);
lean_closure_set(v___f_1334_, 1, v___x_1327_);
lean_closure_set(v___f_1334_, 2, v_alts_1328_);
lean_closure_set(v___f_1334_, 3, v___f_1325_);
lean_closure_set(v___f_1334_, 4, v_numFields_1332_);
lean_closure_set(v___f_1334_, 5, v_head_1323_);
lean_closure_set(v___f_1334_, 6, v___f_1326_);
v___x_1335_ = 0;
v___x_1336_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg(v_type_1333_, v___f_1334_, v___x_1335_, v___x_1335_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v_a_1337_; size_t v_sz_1338_; size_t v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_a_1337_);
lean_dec_ref_known(v___x_1336_, 1);
v_sz_1338_ = lean_array_size(v_a_1337_);
v___x_1339_ = ((size_t)0ULL);
v___x_1340_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__6(v_sz_1338_, v___x_1339_, v_a_1337_);
v___x_1341_ = l_Array_append___redArg(v_b_1314_, v___x_1340_);
lean_dec_ref(v___x_1340_);
v_as_x27_1313_ = v_tail_1324_;
v_b_1314_ = v___x_1341_;
goto _start;
}
else
{
lean_dec_ref(v_b_1314_);
lean_dec_ref(v_indVal_1312_);
return v___x_1336_;
}
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
lean_dec_ref(v_b_1314_);
lean_dec_ref(v_indVal_1312_);
v_a_1343_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1329_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1329_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___boxed(lean_object* v_indVal_1351_, lean_object* v_as_x27_1352_, lean_object* v_b_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg(v_indVal_1351_, v_as_x27_1352_, v_b_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v_as_x27_1352_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts(lean_object* v_indVal_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_){
_start:
{
lean_object* v_ctors_1370_; lean_object* v_alts_1371_; lean_object* v___x_1372_; 
v_ctors_1370_ = lean_ctor_get(v_indVal_1362_, 4);
lean_inc(v_ctors_1370_);
v_alts_1371_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__2));
v___x_1372_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg(v_indVal_1362_, v_ctors_1370_, v_alts_1371_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
lean_dec(v_ctors_1370_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1382_; 
v_a_1373_ = lean_ctor_get(v___x_1372_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1372_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1375_ = v___x_1372_;
v_isShared_1376_ = v_isSharedCheck_1382_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1372_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1382_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1380_; 
v___x_1377_ = lean_array_pop(v_a_1373_);
v___x_1378_ = lean_array_pop(v___x_1377_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 0, v___x_1378_);
v___x_1380_ = v___x_1375_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1378_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
else
{
return v___x_1372_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts___boxed(lean_object* v_indVal_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts(v_indVal_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_, v_a_1388_, v_a_1389_);
lean_dec(v_a_1389_);
lean_dec_ref(v_a_1388_);
lean_dec(v_a_1387_);
lean_dec_ref(v_a_1386_);
lean_dec(v_a_1385_);
lean_dec_ref(v_a_1384_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2(lean_object* v_upperBound_1392_, lean_object* v___x_1393_, lean_object* v_xs_1394_, lean_object* v_a_1395_, lean_object* v_inst_1396_, lean_object* v_R_1397_, lean_object* v_a_1398_, lean_object* v_b_1399_, lean_object* v_c_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg(v_upperBound_1392_, v___x_1393_, v_xs_1394_, v_a_1395_, v_a_1398_, v_b_1399_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___boxed(lean_object* v_upperBound_1409_, lean_object* v___x_1410_, lean_object* v_xs_1411_, lean_object* v_a_1412_, lean_object* v_inst_1413_, lean_object* v_R_1414_, lean_object* v_a_1415_, lean_object* v_b_1416_, lean_object* v_c_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2(v_upperBound_1409_, v___x_1410_, v_xs_1411_, v_a_1412_, v_inst_1413_, v_R_1414_, v_a_1415_, v_b_1416_, v_c_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec_ref(v_a_1412_);
lean_dec_ref(v_xs_1411_);
lean_dec(v___x_1410_);
lean_dec(v_upperBound_1409_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3(lean_object* v_upperBound_1426_, lean_object* v_inst_1427_, lean_object* v_R_1428_, lean_object* v_a_1429_, lean_object* v_b_1430_, lean_object* v_c_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3___redArg(v_upperBound_1426_, v_a_1429_, v_b_1430_, v___y_1436_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3___boxed(lean_object* v_upperBound_1440_, lean_object* v_inst_1441_, lean_object* v_R_1442_, lean_object* v_a_1443_, lean_object* v_b_1444_, lean_object* v_c_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3(v_upperBound_1440_, v_inst_1441_, v_R_1442_, v_a_1443_, v_b_1444_, v_c_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v_upperBound_1440_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4(lean_object* v_upperBound_1454_, lean_object* v_inst_1455_, lean_object* v_R_1456_, lean_object* v_a_1457_, lean_object* v_b_1458_, lean_object* v_c_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4___redArg(v_upperBound_1454_, v_a_1457_, v_b_1458_, v___y_1464_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4___boxed(lean_object* v_upperBound_1468_, lean_object* v_inst_1469_, lean_object* v_R_1470_, lean_object* v_a_1471_, lean_object* v_b_1472_, lean_object* v_c_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4(v_upperBound_1468_, v_inst_1469_, v_R_1470_, v_a_1471_, v_b_1472_, v_c_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v_upperBound_1468_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7(lean_object* v_indVal_1482_, lean_object* v_as_1483_, lean_object* v_as_x27_1484_, lean_object* v_b_1485_, lean_object* v_a_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg(v_indVal_1482_, v_as_x27_1484_, v_b_1485_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___boxed(lean_object* v_indVal_1495_, lean_object* v_as_1496_, lean_object* v_as_x27_1497_, lean_object* v_b_1498_, lean_object* v_a_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7(v_indVal_1495_, v_as_1496_, v_as_x27_1497_, v_b_1498_, v_a_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v_as_x27_1497_);
lean_dec(v_as_1496_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0(lean_object* v_00_u03b1_1508_, lean_object* v_msg_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0___redArg(v_msg_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1518_, lean_object* v_msg_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0(v_00_u03b1_1518_, v_msg_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3(lean_object* v_msgData_1528_, lean_object* v_macroStack_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(v_msgData_1528_, v_macroStack_1529_, v___y_1534_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___boxed(lean_object* v_msgData_1538_, lean_object* v_macroStack_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3(v_msgData_1538_, v_macroStack_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld(lean_object* v_header_1561_, lean_object* v_indVal_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_){
_start:
{
lean_object* v___x_1570_; 
lean_inc_ref(v_indVal_1562_);
v___x_1570_ = l_Lean_Elab_Deriving_mkDiscrs(v_header_1561_, v_indVal_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_a_1571_; lean_object* v___x_1572_; 
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_a_1571_);
lean_dec_ref_known(v___x_1570_, 1);
v___x_1572_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts(v_indVal_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1603_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1575_ = v___x_1572_;
v_isShared_1576_ = v_isSharedCheck_1603_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1572_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1603_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v_ref_1577_; uint8_t v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; size_t v_sz_1586_; size_t v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1601_; 
v_ref_1577_ = lean_ctor_get(v_a_1567_, 2);
v___x_1578_ = 0;
v___x_1579_ = l_Lean_SourceInfo_fromRef(v_ref_1577_, v___x_1578_);
v___x_1580_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__0));
v___x_1581_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__1));
lean_inc_n(v___x_1579_, 6);
v___x_1582_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1579_);
lean_ctor_set(v___x_1582_, 1, v___x_1580_);
v___x_1583_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_1584_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3);
v___x_1585_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1579_);
lean_ctor_set(v___x_1585_, 1, v___x_1583_);
lean_ctor_set(v___x_1585_, 2, v___x_1584_);
v_sz_1586_ = lean_array_size(v_a_1571_);
v___x_1587_ = ((size_t)0ULL);
v___x_1588_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__1(v_sz_1586_, v___x_1587_, v_a_1571_);
v___x_1589_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__16, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__16_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__16);
v___x_1590_ = l_Lean_mkSepArray(v___x_1588_, v___x_1589_);
lean_dec_ref(v___x_1588_);
v___x_1591_ = l_Array_append___redArg(v___x_1584_, v___x_1590_);
lean_dec_ref(v___x_1590_);
v___x_1592_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1592_, 0, v___x_1579_);
lean_ctor_set(v___x_1592_, 1, v___x_1583_);
lean_ctor_set(v___x_1592_, 2, v___x_1591_);
v___x_1593_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__2));
v___x_1594_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1579_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v___x_1595_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__4));
v___x_1596_ = l_Array_append___redArg(v___x_1584_, v_a_1573_);
lean_dec(v_a_1573_);
v___x_1597_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1579_);
lean_ctor_set(v___x_1597_, 1, v___x_1583_);
lean_ctor_set(v___x_1597_, 2, v___x_1596_);
v___x_1598_ = l_Lean_Syntax_node1(v___x_1579_, v___x_1595_, v___x_1597_);
lean_inc_ref(v___x_1585_);
v___x_1599_ = l_Lean_Syntax_node6(v___x_1579_, v___x_1581_, v___x_1582_, v___x_1585_, v___x_1585_, v___x_1592_, v___x_1594_, v___x_1598_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 0, v___x_1599_);
v___x_1601_ = v___x_1575_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1599_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
lean_dec(v_a_1571_);
v_a_1604_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1572_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1572_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
lean_dec_ref(v_indVal_1562_);
v_a_1612_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1570_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1570_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___boxed(lean_object* v_header_1620_, lean_object* v_indVal_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld(v_header_1620_, v_indVal_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_);
lean_dec(v_a_1627_);
lean_dec_ref(v_a_1626_);
lean_dec(v_a_1625_);
lean_dec_ref(v_a_1624_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
return v_res_1629_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Lean_Elab_Term_instInhabitedTermElabM___redArg();
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1(lean_object* v_msg_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_24886__overap_1640_; lean_object* v___x_1641_; 
v___x_1639_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___closed__0, &l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___closed__0);
v___x_24886__overap_1640_ = lean_panic_fn_borrowed(v___x_1639_, v_msg_1631_);
lean_inc(v___y_1637_);
lean_inc_ref(v___y_1636_);
lean_inc(v___y_1635_);
lean_inc_ref(v___y_1634_);
lean_inc(v___y_1633_);
lean_inc_ref(v___y_1632_);
v___x_1641_ = lean_apply_7(v___x_24886__overap_1640_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, lean_box(0));
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___boxed(lean_object* v_msg_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1(v_msg_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg___lam__0(uint8_t v_a_1651_, lean_object* v___x_1652_, lean_object* v___x_1653_, lean_object* v_snd_1654_, lean_object* v_rhs_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v_toCold_1663_; lean_object* v_ref_1664_; lean_object* v_quotContext_1665_; lean_object* v_currMacroScope_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v_toCold_1663_ = lean_ctor_get(v___y_1660_, 0);
v_ref_1664_ = lean_ctor_get(v___y_1660_, 2);
v_quotContext_1665_ = lean_ctor_get(v_toCold_1663_, 8);
v_currMacroScope_1666_ = lean_ctor_get(v_toCold_1663_, 9);
v___x_1667_ = l_Lean_SourceInfo_fromRef(v_ref_1664_, v_a_1651_);
v___x_1668_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3));
v___x_1669_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__5);
v___x_1670_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__8));
lean_inc_n(v_currMacroScope_1666_, 3);
lean_inc_n(v_quotContext_1665_, 3);
v___x_1671_ = l_Lean_addMacroScope(v_quotContext_1665_, v___x_1670_, v_currMacroScope_1666_);
v___x_1672_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__12));
lean_inc_n(v___x_1667_, 11);
v___x_1673_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1673_, 0, v___x_1667_);
lean_ctor_set(v___x_1673_, 1, v___x_1669_);
lean_ctor_set(v___x_1673_, 2, v___x_1671_);
lean_ctor_set(v___x_1673_, 3, v___x_1672_);
v___x_1674_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_1675_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__16));
v___x_1676_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18));
v___x_1677_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__19));
v___x_1678_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1667_);
lean_ctor_set(v___x_1678_, 1, v___x_1677_);
v___x_1679_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__21));
v___x_1680_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23);
v___x_1681_ = lean_box(0);
v___x_1682_ = l_Lean_addMacroScope(v_quotContext_1665_, v___x_1681_, v_currMacroScope_1666_);
v___x_1683_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__33));
v___x_1684_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1667_);
lean_ctor_set(v___x_1684_, 1, v___x_1680_);
lean_ctor_set(v___x_1684_, 2, v___x_1682_);
lean_ctor_set(v___x_1684_, 3, v___x_1683_);
v___x_1685_ = l_Lean_Syntax_node1(v___x_1667_, v___x_1679_, v___x_1684_);
v___x_1686_ = l_Lean_Syntax_node2(v___x_1667_, v___x_1676_, v___x_1678_, v___x_1685_);
v___x_1687_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35);
v___x_1688_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__36));
v___x_1689_ = l_Lean_addMacroScope(v_quotContext_1665_, v___x_1688_, v_currMacroScope_1666_);
v___x_1690_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__39));
v___x_1691_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1667_);
lean_ctor_set(v___x_1691_, 1, v___x_1687_);
lean_ctor_set(v___x_1691_, 2, v___x_1689_);
lean_ctor_set(v___x_1691_, 3, v___x_1690_);
v___x_1692_ = l_Lean_Syntax_node2(v___x_1667_, v___x_1674_, v___x_1652_, v___x_1653_);
v___x_1693_ = l_Lean_Syntax_node2(v___x_1667_, v___x_1668_, v___x_1691_, v___x_1692_);
v___x_1694_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__40));
v___x_1695_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1667_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
v___x_1696_ = l_Lean_Syntax_node3(v___x_1667_, v___x_1675_, v___x_1686_, v___x_1693_, v___x_1695_);
v___x_1697_ = l_Lean_Syntax_node2(v___x_1667_, v___x_1674_, v___x_1696_, v_rhs_1655_);
v___x_1698_ = l_Lean_Syntax_node2(v___x_1667_, v___x_1668_, v___x_1673_, v___x_1697_);
lean_inc(v___y_1661_);
lean_inc_ref(v___y_1660_);
lean_inc(v___y_1659_);
lean_inc_ref(v___y_1658_);
lean_inc(v___y_1657_);
lean_inc_ref(v___y_1656_);
v___x_1699_ = lean_apply_8(v_snd_1654_, v___x_1698_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, lean_box(0));
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg___lam__0___boxed(lean_object* v_a_1700_, lean_object* v___x_1701_, lean_object* v___x_1702_, lean_object* v_snd_1703_, lean_object* v_rhs_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
uint8_t v_a_26174__boxed_1712_; lean_object* v_res_1713_; 
v_a_26174__boxed_1712_ = lean_unbox(v_a_1700_);
v_res_1713_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg___lam__0(v_a_26174__boxed_1712_, v___x_1701_, v___x_1702_, v_snd_1703_, v_rhs_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg(lean_object* v_upperBound_1715_, lean_object* v_indVal_1716_, lean_object* v_xs_1717_, lean_object* v_a_1718_, lean_object* v_a_1719_, lean_object* v_b_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v_a_1727_; uint8_t v___x_1731_; 
v___x_1731_ = lean_nat_dec_lt(v_a_1719_, v_upperBound_1715_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; 
lean_dec(v_a_1719_);
v___x_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1732_, 0, v_b_1720_);
return v___x_1732_;
}
else
{
lean_object* v_snd_1733_; lean_object* v_fst_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1835_; 
v_snd_1733_ = lean_ctor_get(v_b_1720_, 1);
v_fst_1734_ = lean_ctor_get(v_b_1720_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v_b_1720_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1736_ = v_b_1720_;
v_isShared_1737_ = v_isSharedCheck_1835_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_snd_1733_);
lean_inc(v_fst_1734_);
lean_dec(v_b_1720_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1835_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v_fst_1738_; lean_object* v_snd_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1834_; 
v_fst_1738_ = lean_ctor_get(v_snd_1733_, 0);
v_snd_1739_ = lean_ctor_get(v_snd_1733_, 1);
v_isSharedCheck_1834_ = !lean_is_exclusive(v_snd_1733_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1741_ = v_snd_1733_;
v_isShared_1742_ = v_isSharedCheck_1834_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_snd_1739_);
lean_inc(v_fst_1738_);
lean_dec(v_snd_1733_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1834_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v_numParams_1743_; lean_object* v_lctx_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; 
v_numParams_1743_ = lean_ctor_get(v_indVal_1716_, 1);
v_lctx_1744_ = lean_ctor_get(v___y_1721_, 2);
v___x_1745_ = l_Lean_instInhabitedExpr;
v___x_1746_ = lean_nat_add(v_numParams_1743_, v_a_1719_);
v___x_1747_ = lean_array_get_borrowed(v___x_1745_, v_xs_1717_, v___x_1746_);
lean_dec(v___x_1746_);
lean_inc(v___x_1747_);
lean_inc_ref(v_lctx_1744_);
v___x_1748_ = l_Lean_Meta_occursOrInType(v_lctx_1744_, v___x_1747_, v_a_1718_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = l_Lean_Expr_fvarId_x21(v___x_1747_);
v___x_1750_ = l_Lean_FVarId_getUserName___redArg(v___x_1749_, v___y_1721_, v___y_1723_, v___y_1724_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1752_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc_n(v_a_1751_, 2);
lean_dec_ref_known(v___x_1750_, 1);
v___x_1752_ = l_Lean_Core_mkFreshUserName(v_a_1751_, v___y_1723_, v___y_1724_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
lean_inc(v_a_1753_);
lean_dec_ref_known(v___x_1752_, 1);
v___x_1754_ = l_Lean_mkIdent(v_a_1753_);
v___x_1755_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg___closed__0));
v___x_1756_ = lean_name_append_after(v_a_1751_, v___x_1755_);
v___x_1757_ = l_Lean_Core_mkFreshUserName(v___x_1756_, v___y_1723_, v___y_1724_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
lean_dec_ref_known(v___x_1757_, 1);
v___x_1759_ = l_Lean_mkIdent(v_a_1758_);
lean_inc(v___x_1754_);
v___x_1760_ = lean_array_push(v_fst_1734_, v___x_1754_);
lean_inc(v___x_1759_);
v___x_1761_ = lean_array_push(v_fst_1738_, v___x_1759_);
lean_inc(v___y_1724_);
lean_inc_ref(v___y_1723_);
lean_inc(v___y_1722_);
lean_inc_ref(v___y_1721_);
lean_inc(v___x_1747_);
v___x_1762_ = lean_infer_type(v___x_1747_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v___x_1764_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc(v_a_1763_);
lean_dec_ref_known(v___x_1762_, 1);
v___x_1764_ = l_Lean_Meta_isProp(v_a_1763_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; uint8_t v___x_1766_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref_known(v___x_1764_, 1);
v___x_1766_ = lean_unbox(v_a_1765_);
if (v___x_1766_ == 0)
{
lean_object* v___f_1767_; lean_object* v___x_1769_; 
v___f_1767_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_1767_, 0, v_a_1765_);
lean_closure_set(v___f_1767_, 1, v___x_1754_);
lean_closure_set(v___f_1767_, 2, v___x_1759_);
lean_closure_set(v___f_1767_, 3, v_snd_1739_);
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 1, v___f_1767_);
lean_ctor_set(v___x_1741_, 0, v___x_1761_);
v___x_1769_ = v___x_1741_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1761_);
lean_ctor_set(v_reuseFailAlloc_1773_, 1, v___f_1767_);
v___x_1769_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
lean_object* v___x_1771_; 
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 1, v___x_1769_);
lean_ctor_set(v___x_1736_, 0, v___x_1760_);
v___x_1771_ = v___x_1736_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1760_);
lean_ctor_set(v_reuseFailAlloc_1772_, 1, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
v_a_1727_ = v___x_1771_;
goto v___jp_1726_;
}
}
}
else
{
lean_object* v___x_1775_; 
lean_dec(v_a_1765_);
lean_dec(v___x_1759_);
lean_dec(v___x_1754_);
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1761_);
v___x_1775_ = v___x_1741_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1761_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_snd_1739_);
v___x_1775_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
lean_object* v___x_1777_; 
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 1, v___x_1775_);
lean_ctor_set(v___x_1736_, 0, v___x_1760_);
v___x_1777_ = v___x_1736_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1760_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v___x_1775_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
v_a_1727_ = v___x_1777_;
goto v___jp_1726_;
}
}
}
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
lean_dec_ref(v___x_1761_);
lean_dec_ref(v___x_1760_);
lean_dec(v___x_1759_);
lean_dec(v___x_1754_);
lean_del_object(v___x_1741_);
lean_dec(v_snd_1739_);
lean_del_object(v___x_1736_);
lean_dec(v_a_1719_);
v_a_1780_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1764_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1764_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_dec_ref(v___x_1761_);
lean_dec_ref(v___x_1760_);
lean_dec(v___x_1759_);
lean_dec(v___x_1754_);
lean_del_object(v___x_1741_);
lean_dec(v_snd_1739_);
lean_del_object(v___x_1736_);
lean_dec(v_a_1719_);
v_a_1788_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1762_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1762_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
lean_dec(v___x_1754_);
lean_del_object(v___x_1741_);
lean_dec(v_snd_1739_);
lean_dec(v_fst_1738_);
lean_del_object(v___x_1736_);
lean_dec(v_fst_1734_);
lean_dec(v_a_1719_);
v_a_1796_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1757_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1757_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
else
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1811_; 
lean_dec(v_a_1751_);
lean_del_object(v___x_1741_);
lean_dec(v_snd_1739_);
lean_dec(v_fst_1738_);
lean_del_object(v___x_1736_);
lean_dec(v_fst_1734_);
lean_dec(v_a_1719_);
v_a_1804_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1806_ = v___x_1752_;
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1752_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1809_; 
if (v_isShared_1807_ == 0)
{
v___x_1809_ = v___x_1806_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_a_1804_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
lean_del_object(v___x_1741_);
lean_dec(v_snd_1739_);
lean_dec(v_fst_1738_);
lean_del_object(v___x_1736_);
lean_dec(v_fst_1734_);
lean_dec(v_a_1719_);
v_a_1812_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1750_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1750_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
else
{
lean_object* v_ref_1820_; uint8_t v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1829_; 
v_ref_1820_ = lean_ctor_get(v___y_1723_, 2);
v___x_1821_ = 0;
v___x_1822_ = l_Lean_SourceInfo_fromRef(v_ref_1820_, v___x_1821_);
v___x_1823_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8));
v___x_1824_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__9));
lean_inc(v___x_1822_);
v___x_1825_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1822_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = l_Lean_Syntax_node1(v___x_1822_, v___x_1823_, v___x_1825_);
v___x_1827_ = lean_array_push(v_fst_1734_, v___x_1826_);
if (v_isShared_1742_ == 0)
{
v___x_1829_ = v___x_1741_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_fst_1738_);
lean_ctor_set(v_reuseFailAlloc_1833_, 1, v_snd_1739_);
v___x_1829_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
lean_object* v___x_1831_; 
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 1, v___x_1829_);
lean_ctor_set(v___x_1736_, 0, v___x_1827_);
v___x_1831_ = v___x_1736_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1827_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v___x_1829_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
v_a_1727_ = v___x_1831_;
goto v___jp_1726_;
}
}
}
}
}
}
v___jp_1726_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1728_ = lean_unsigned_to_nat(1u);
v___x_1729_ = lean_nat_add(v_a_1719_, v___x_1728_);
lean_dec(v_a_1719_);
v_a_1719_ = v___x_1729_;
v_b_1720_ = v_a_1727_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg___boxed(lean_object* v_upperBound_1836_, lean_object* v_indVal_1837_, lean_object* v_xs_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_b_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg(v_upperBound_1836_, v_indVal_1837_, v_xs_1838_, v_a_1839_, v_a_1840_, v_b_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec_ref(v_a_1839_);
lean_dec_ref(v_xs_1838_);
lean_dec_ref(v_indVal_1837_);
lean_dec(v_upperBound_1836_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2(lean_object* v___f_1866_, lean_object* v_numFields_1867_, lean_object* v_indVal_1868_, lean_object* v___f_1869_, lean_object* v_xs_1870_, lean_object* v_type_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Lean_Core_betaReduce(v_type_1871_, v___y_1876_, v___y_1877_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v_a_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v_a_1880_ = lean_ctor_get(v___x_1879_, 0);
lean_inc(v_a_1880_);
lean_dec_ref_known(v___x_1879_, 1);
v___x_1881_ = lean_unsigned_to_nat(0u);
v___x_1882_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__2));
v___x_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
lean_ctor_set(v___x_1883_, 1, v___f_1866_);
v___x_1884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1882_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
v___x_1885_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg(v_numFields_1867_, v_indVal_1868_, v_xs_1870_, v_a_1880_, v___x_1881_, v___x_1884_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
lean_dec(v_a_1880_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v_snd_1887_; lean_object* v_toCold_1888_; lean_object* v_fst_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1989_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref_known(v___x_1885_, 1);
v_snd_1887_ = lean_ctor_get(v_a_1886_, 1);
lean_inc(v_snd_1887_);
v_toCold_1888_ = lean_ctor_get(v___y_1876_, 0);
v_fst_1889_ = lean_ctor_get(v_a_1886_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v_a_1886_);
if (v_isSharedCheck_1989_ == 0)
{
lean_object* v_unused_1990_; 
v_unused_1990_ = lean_ctor_get(v_a_1886_, 1);
lean_dec(v_unused_1990_);
v___x_1891_ = v_a_1886_;
v_isShared_1892_ = v_isSharedCheck_1989_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_fst_1889_);
lean_dec(v_a_1886_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1989_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v_fst_1893_; lean_object* v_snd_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1988_; 
v_fst_1893_ = lean_ctor_get(v_snd_1887_, 0);
v_snd_1894_ = lean_ctor_get(v_snd_1887_, 1);
v_isSharedCheck_1988_ = !lean_is_exclusive(v_snd_1887_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1896_ = v_snd_1887_;
v_isShared_1897_ = v_isSharedCheck_1988_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_snd_1894_);
lean_inc(v_fst_1893_);
lean_dec(v_snd_1887_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1988_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v_ref_1898_; lean_object* v_quotContext_1899_; lean_object* v_currMacroScope_1900_; uint8_t v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v_ref_1898_ = lean_ctor_get(v___y_1876_, 2);
v_quotContext_1899_ = lean_ctor_get(v_toCold_1888_, 8);
v_currMacroScope_1900_ = lean_ctor_get(v_toCold_1888_, 9);
v___x_1901_ = 0;
v___x_1902_ = l_Lean_SourceInfo_fromRef(v_ref_1898_, v___x_1901_);
v___x_1903_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__5);
v___x_1904_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__7));
lean_inc(v_currMacroScope_1900_);
lean_inc(v_quotContext_1899_);
v___x_1905_ = l_Lean_addMacroScope(v_quotContext_1899_, v___x_1904_, v_currMacroScope_1900_);
v___x_1906_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11));
v___x_1907_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1902_);
lean_ctor_set(v___x_1907_, 1, v___x_1903_);
lean_ctor_set(v___x_1907_, 2, v___x_1905_);
lean_ctor_set(v___x_1907_, 3, v___x_1906_);
lean_inc(v___y_1877_);
lean_inc_ref(v___y_1876_);
lean_inc(v___y_1875_);
lean_inc_ref(v___y_1874_);
lean_inc(v___y_1873_);
lean_inc_ref(v___y_1872_);
v___x_1908_ = lean_apply_8(v_snd_1894_, v___x_1907_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, lean_box(0));
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; lean_object* v_ctorArgs1_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___x_1957_; uint8_t v___x_1958_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_a_1909_);
lean_dec_ref_known(v___x_1908_, 1);
v___x_1957_ = lean_array_get_size(v_fst_1889_);
v___x_1958_ = lean_nat_dec_eq(v___x_1957_, v___x_1881_);
if (v___x_1958_ == 0)
{
v_ctorArgs1_1911_ = v_fst_1889_;
v___y_1912_ = v___y_1872_;
v___y_1913_ = v___y_1873_;
v___y_1914_ = v___y_1874_;
v___y_1915_ = v___y_1875_;
v___y_1916_ = v___y_1876_;
v___y_1917_ = v___y_1877_;
goto v___jp_1910_;
}
else
{
lean_object* v___x_1959_; 
lean_inc_ref(v___f_1869_);
lean_inc(v___y_1877_);
lean_inc_ref(v___y_1876_);
lean_inc(v___y_1875_);
lean_inc_ref(v___y_1874_);
lean_inc(v___y_1873_);
lean_inc_ref(v___y_1872_);
v___x_1959_ = lean_apply_7(v___f_1869_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, lean_box(0));
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_a_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc_n(v_a_1960_, 7);
lean_dec_ref_known(v___x_1959_, 1);
v___x_1961_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__5));
v___x_1962_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18));
v___x_1963_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__19));
v___x_1964_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1964_, 0, v_a_1960_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__21));
v___x_1966_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23);
v___x_1967_ = lean_box(0);
lean_inc(v_currMacroScope_1900_);
lean_inc(v_quotContext_1899_);
v___x_1968_ = l_Lean_addMacroScope(v_quotContext_1899_, v___x_1967_, v_currMacroScope_1900_);
v___x_1969_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__33));
v___x_1970_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1970_, 0, v_a_1960_);
lean_ctor_set(v___x_1970_, 1, v___x_1966_);
lean_ctor_set(v___x_1970_, 2, v___x_1968_);
lean_ctor_set(v___x_1970_, 3, v___x_1969_);
v___x_1971_ = l_Lean_Syntax_node1(v_a_1960_, v___x_1965_, v___x_1970_);
v___x_1972_ = l_Lean_Syntax_node2(v_a_1960_, v___x_1962_, v___x_1964_, v___x_1971_);
v___x_1973_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_1974_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3);
v___x_1975_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1975_, 0, v_a_1960_);
lean_ctor_set(v___x_1975_, 1, v___x_1973_);
lean_ctor_set(v___x_1975_, 2, v___x_1974_);
v___x_1976_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__40));
v___x_1977_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1977_, 0, v_a_1960_);
lean_ctor_set(v___x_1977_, 1, v___x_1976_);
v___x_1978_ = l_Lean_Syntax_node3(v_a_1960_, v___x_1961_, v___x_1972_, v___x_1975_, v___x_1977_);
v___x_1979_ = lean_array_push(v_fst_1889_, v___x_1978_);
v_ctorArgs1_1911_ = v___x_1979_;
v___y_1912_ = v___y_1872_;
v___y_1913_ = v___y_1873_;
v___y_1914_ = v___y_1874_;
v___y_1915_ = v___y_1875_;
v___y_1916_ = v___y_1876_;
v___y_1917_ = v___y_1877_;
goto v___jp_1910_;
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec(v_a_1909_);
lean_del_object(v___x_1896_);
lean_dec(v_fst_1893_);
lean_del_object(v___x_1891_);
lean_dec(v_fst_1889_);
lean_dec_ref(v___f_1869_);
v_a_1980_ = lean_ctor_get(v___x_1959_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1959_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1959_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
v___jp_1910_:
{
lean_object* v___x_1918_; 
lean_inc(v___y_1917_);
lean_inc_ref(v___y_1916_);
lean_inc(v___y_1915_);
lean_inc_ref(v___y_1914_);
lean_inc(v___y_1913_);
lean_inc_ref(v___y_1912_);
v___x_1918_ = lean_apply_7(v___f_1869_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, lean_box(0));
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1948_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1921_ = v___x_1918_;
v_isShared_1922_ = v_isSharedCheck_1948_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1918_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1948_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1926_; 
v___x_1923_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1));
v___x_1924_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__2));
lean_inc(v_a_1919_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set_tag(v___x_1896_, 2);
lean_ctor_set(v___x_1896_, 1, v___x_1924_);
lean_ctor_set(v___x_1896_, 0, v_a_1919_);
v___x_1926_ = v___x_1896_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1919_);
lean_ctor_set(v_reuseFailAlloc_1947_, 1, v___x_1924_);
v___x_1926_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1930_; 
v___x_1927_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__0));
v___x_1928_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__1));
lean_inc(v_a_1919_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set_tag(v___x_1891_, 2);
lean_ctor_set(v___x_1891_, 1, v___x_1927_);
lean_ctor_set(v___x_1891_, 0, v_a_1919_);
v___x_1930_ = v___x_1891_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1919_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v___x_1927_);
v___x_1930_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1944_; 
v___x_1931_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__3));
v___x_1932_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_1933_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3);
v___x_1934_ = l_Array_append___redArg(v___x_1933_, v_ctorArgs1_1911_);
lean_dec_ref(v_ctorArgs1_1911_);
v___x_1935_ = l_Array_append___redArg(v___x_1934_, v_fst_1893_);
lean_dec(v_fst_1893_);
lean_inc_n(v_a_1919_, 5);
v___x_1936_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1936_, 0, v_a_1919_);
lean_ctor_set(v___x_1936_, 1, v___x_1932_);
lean_ctor_set(v___x_1936_, 2, v___x_1935_);
v___x_1937_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1937_, 0, v_a_1919_);
lean_ctor_set(v___x_1937_, 1, v___x_1932_);
lean_ctor_set(v___x_1937_, 2, v___x_1933_);
v___x_1938_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__17));
v___x_1939_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1939_, 0, v_a_1919_);
lean_ctor_set(v___x_1939_, 1, v___x_1938_);
v___x_1940_ = l_Lean_Syntax_node4(v_a_1919_, v___x_1931_, v___x_1936_, v___x_1937_, v___x_1939_, v_a_1909_);
v___x_1941_ = l_Lean_Syntax_node2(v_a_1919_, v___x_1928_, v___x_1930_, v___x_1940_);
v___x_1942_ = l_Lean_Syntax_node2(v_a_1919_, v___x_1923_, v___x_1926_, v___x_1941_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 0, v___x_1942_);
v___x_1944_ = v___x_1921_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1942_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
}
else
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1956_; 
lean_dec_ref(v_ctorArgs1_1911_);
lean_dec(v_a_1909_);
lean_del_object(v___x_1896_);
lean_dec(v_fst_1893_);
lean_del_object(v___x_1891_);
v_a_1949_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1951_ = v___x_1918_;
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1918_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1956_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___x_1954_; 
if (v_isShared_1952_ == 0)
{
v___x_1954_ = v___x_1951_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
}
else
{
lean_del_object(v___x_1896_);
lean_dec(v_fst_1893_);
lean_del_object(v___x_1891_);
lean_dec(v_fst_1889_);
lean_dec_ref(v___f_1869_);
return v___x_1908_;
}
}
}
}
else
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1998_; 
lean_dec_ref(v___f_1869_);
v_a_1991_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1993_ = v___x_1885_;
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1885_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1996_; 
if (v_isShared_1994_ == 0)
{
v___x_1996_ = v___x_1993_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_a_1991_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
else
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
lean_dec_ref(v___f_1869_);
lean_dec_ref(v___f_1866_);
v_a_1999_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1879_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1879_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___boxed(lean_object* v___f_2007_, lean_object* v_numFields_2008_, lean_object* v_indVal_2009_, lean_object* v___f_2010_, lean_object* v_xs_2011_, lean_object* v_type_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2(v___f_2007_, v_numFields_2008_, v_indVal_2009_, v___f_2010_, v_xs_2011_, v_type_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_, v___y_2018_);
lean_dec(v___y_2018_);
lean_dec_ref(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec_ref(v___y_2015_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec_ref(v_xs_2011_);
lean_dec_ref(v_indVal_2009_);
lean_dec(v_numFields_2008_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__0(lean_object* v___x_2021_, lean_object* v_ctors_2022_, lean_object* v___f_2023_, lean_object* v_indVal_2024_, lean_object* v___f_2025_, lean_object* v_x_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = l_List_get_x21Internal___redArg(v___x_2021_, v_ctors_2022_, v_x_2026_);
v___x_2035_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0(v___x_2034_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v_a_2036_; lean_object* v_toConstantVal_2037_; lean_object* v_numFields_2038_; lean_object* v_type_2039_; lean_object* v___f_2040_; uint8_t v___x_2041_; lean_object* v___x_2042_; 
v_a_2036_ = lean_ctor_get(v___x_2035_, 0);
lean_inc(v_a_2036_);
lean_dec_ref_known(v___x_2035_, 1);
v_toConstantVal_2037_ = lean_ctor_get(v_a_2036_, 0);
lean_inc_ref(v_toConstantVal_2037_);
v_numFields_2038_ = lean_ctor_get(v_a_2036_, 4);
lean_inc(v_numFields_2038_);
lean_dec(v_a_2036_);
v_type_2039_ = lean_ctor_get(v_toConstantVal_2037_, 2);
lean_inc_ref(v_type_2039_);
lean_dec_ref(v_toConstantVal_2037_);
v___f_2040_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___boxed), 13, 4);
lean_closure_set(v___f_2040_, 0, v___f_2023_);
lean_closure_set(v___f_2040_, 1, v_numFields_2038_);
lean_closure_set(v___f_2040_, 2, v_indVal_2024_);
lean_closure_set(v___f_2040_, 3, v___f_2025_);
v___x_2041_ = 0;
v___x_2042_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg(v_type_2039_, v___f_2040_, v___x_2041_, v___x_2041_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
return v___x_2042_;
}
else
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
lean_dec_ref(v___f_2025_);
lean_dec_ref(v_indVal_2024_);
lean_dec_ref(v___f_2023_);
v_a_2043_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_2035_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2035_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__0___boxed(lean_object* v___x_2051_, lean_object* v_ctors_2052_, lean_object* v___f_2053_, lean_object* v_indVal_2054_, lean_object* v___f_2055_, lean_object* v_x_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v_res_2064_; 
v_res_2064_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__0(v___x_2051_, v_ctors_2052_, v___f_2053_, v_indVal_2054_, v___f_2055_, v_x_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_, v___y_2062_);
lean_dec(v___y_2062_);
lean_dec_ref(v___y_2061_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v_ctors_2052_);
lean_dec(v___x_2051_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2___redArg(lean_object* v_f_2065_, lean_object* v_n_2066_, lean_object* v_x_2067_, lean_object* v_i_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
uint8_t v___x_2076_; 
v___x_2076_ = lean_nat_dec_lt(v_i_2068_, v_n_2066_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; 
lean_dec(v_i_2068_);
lean_dec_ref(v_f_2065_);
v___x_2077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2077_, 0, v_x_2067_);
return v___x_2077_;
}
else
{
lean_object* v___x_2078_; 
lean_inc_ref(v_f_2065_);
lean_inc(v___y_2074_);
lean_inc_ref(v___y_2073_);
lean_inc(v___y_2072_);
lean_inc_ref(v___y_2071_);
lean_inc(v___y_2070_);
lean_inc_ref(v___y_2069_);
lean_inc(v_i_2068_);
v___x_2078_ = lean_apply_8(v_f_2065_, v_i_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, lean_box(0));
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_a_2079_);
lean_dec_ref_known(v___x_2078_, 1);
v___x_2080_ = lean_array_push(v_x_2067_, v_a_2079_);
v___x_2081_ = lean_unsigned_to_nat(1u);
v___x_2082_ = lean_nat_add(v_i_2068_, v___x_2081_);
lean_dec(v_i_2068_);
v_x_2067_ = v___x_2080_;
v_i_2068_ = v___x_2082_;
goto _start;
}
else
{
lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2091_; 
lean_dec(v_i_2068_);
lean_dec_ref(v_x_2067_);
lean_dec_ref(v_f_2065_);
v_a_2084_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2086_ = v___x_2078_;
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_2078_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2089_; 
if (v_isShared_2087_ == 0)
{
v___x_2089_ = v___x_2086_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_a_2084_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2___redArg___boxed(lean_object* v_f_2092_, lean_object* v_n_2093_, lean_object* v_x_2094_, lean_object* v_i_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2___redArg(v_f_2092_, v_n_2093_, v_x_2094_, v_i_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v_n_2093_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2___redArg(lean_object* v_n_2104_, lean_object* v_f_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2113_ = lean_mk_empty_array_with_capacity(v_n_2104_);
v___x_2114_ = lean_unsigned_to_nat(0u);
v___x_2115_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2___redArg(v_f_2105_, v_n_2104_, v___x_2113_, v___x_2114_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2___redArg___boxed(lean_object* v_n_2116_, lean_object* v_f_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2___redArg(v_n_2116_, v_f_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
lean_dec(v_n_2116_);
return v_res_2125_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__3(void){
_start:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2129_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__2));
v___x_2130_ = lean_unsigned_to_nat(2u);
v___x_2131_ = lean_unsigned_to_nat(87u);
v___x_2132_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__1));
v___x_2133_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__0));
v___x_2134_ = l_mkPanicMessageWithDecl(v___x_2133_, v___x_2132_, v___x_2131_, v___x_2130_, v___x_2129_);
return v___x_2134_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__9(void){
_start:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__8));
v___x_2146_ = l_String_toRawSubstring_x27(v___x_2145_);
return v___x_2146_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__27(void){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2193_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__26));
v___x_2194_ = l_String_toRawSubstring_x27(v___x_2193_);
return v___x_2194_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__37(void){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2215_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__36));
v___x_2216_ = l_String_toRawSubstring_x27(v___x_2215_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew(lean_object* v_header_2225_, lean_object* v_indVal_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_){
_start:
{
lean_object* v_targetNames_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2430_; 
v_targetNames_2234_ = lean_ctor_get(v_header_2225_, 2);
v_isSharedCheck_2430_ = !lean_is_exclusive(v_header_2225_);
if (v_isSharedCheck_2430_ == 0)
{
lean_object* v_unused_2431_; lean_object* v_unused_2432_; lean_object* v_unused_2433_; 
v_unused_2431_ = lean_ctor_get(v_header_2225_, 3);
lean_dec(v_unused_2431_);
v_unused_2432_ = lean_ctor_get(v_header_2225_, 1);
lean_dec(v_unused_2432_);
v_unused_2433_ = lean_ctor_get(v_header_2225_, 0);
lean_dec(v_unused_2433_);
v___x_2236_ = v_header_2225_;
v_isShared_2237_ = v_isSharedCheck_2430_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_targetNames_2234_);
lean_dec(v_header_2225_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2430_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; uint8_t v___x_2240_; 
v___x_2238_ = lean_array_get_size(v_targetNames_2234_);
v___x_2239_ = lean_unsigned_to_nat(2u);
v___x_2240_ = lean_nat_dec_eq(v___x_2238_, v___x_2239_);
if (v___x_2240_ == 0)
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
lean_del_object(v___x_2236_);
lean_dec_ref(v_targetNames_2234_);
lean_dec_ref(v_indVal_2226_);
v___x_2241_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__3, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__3_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__3);
v___x_2242_ = l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1(v___x_2241_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
return v___x_2242_;
}
else
{
lean_object* v_toConstantVal_2243_; lean_object* v_ctors_2244_; lean_object* v_name_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2427_; 
v_toConstantVal_2243_ = lean_ctor_get(v_indVal_2226_, 0);
lean_inc_ref(v_toConstantVal_2243_);
v_ctors_2244_ = lean_ctor_get(v_indVal_2226_, 4);
v_name_2245_ = lean_ctor_get(v_toConstantVal_2243_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v_toConstantVal_2243_);
if (v_isSharedCheck_2427_ == 0)
{
lean_object* v_unused_2428_; lean_object* v_unused_2429_; 
v_unused_2428_ = lean_ctor_get(v_toConstantVal_2243_, 2);
lean_dec(v_unused_2428_);
v_unused_2429_ = lean_ctor_get(v_toConstantVal_2243_, 1);
lean_dec(v_unused_2429_);
v___x_2247_ = v_toConstantVal_2243_;
v_isShared_2248_ = v_isSharedCheck_2427_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_name_2245_);
lean_dec(v_toConstantVal_2243_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2427_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
lean_object* v___f_2249_; lean_object* v___f_2250_; lean_object* v___x_2251_; lean_object* v___f_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v_x1_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v_x2_2258_; lean_object* v_ctorIdxName_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___f_2249_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__1));
v___f_2250_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__0));
v___x_2251_ = lean_box(0);
lean_inc_ref(v_indVal_2226_);
lean_inc(v_ctors_2244_);
v___f_2252_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__0___boxed), 13, 5);
lean_closure_set(v___f_2252_, 0, v___x_2251_);
lean_closure_set(v___f_2252_, 1, v_ctors_2244_);
lean_closure_set(v___f_2252_, 2, v___f_2250_);
lean_closure_set(v___f_2252_, 3, v_indVal_2226_);
lean_closure_set(v___f_2252_, 4, v___f_2249_);
v___x_2253_ = lean_unsigned_to_nat(0u);
v___x_2254_ = lean_array_get_borrowed(v___x_2251_, v_targetNames_2234_, v___x_2253_);
lean_inc(v___x_2254_);
v_x1_2255_ = l_Lean_mkIdent(v___x_2254_);
v___x_2256_ = lean_unsigned_to_nat(1u);
v___x_2257_ = lean_array_get(v___x_2251_, v_targetNames_2234_, v___x_2256_);
lean_dec_ref(v_targetNames_2234_);
v_x2_2258_ = l_Lean_mkIdent(v___x_2257_);
lean_inc_n(v_name_2245_, 2);
v_ctorIdxName_2259_ = l_Lean_mkCtorIdxName(v_name_2245_);
v___x_2260_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__5));
v___x_2261_ = l_Lean_Name_append(v_name_2245_, v___x_2260_);
v___x_2262_ = l_Lean_Core_mkFreshUserName(v___x_2261_, v_a_2231_, v_a_2232_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; lean_object* v___x_2264_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
lean_inc_n(v_a_2263_, 2);
lean_dec_ref_known(v___x_2262_, 1);
v___x_2264_ = l_Lean_mkCasesOnSameCtor(v_a_2263_, v_name_2245_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
lean_dec_ref_known(v___x_2264_, 1);
v___x_2265_ = l_Lean_InductiveVal_numCtors(v_indVal_2226_);
lean_dec_ref(v_indVal_2226_);
v___x_2266_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2___redArg(v___x_2265_, v___f_2252_, v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2402_; 
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2269_ = v___x_2266_;
v_isShared_2270_ = v_isSharedCheck_2402_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2266_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2402_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
uint8_t v___x_2271_; 
v___x_2271_ = lean_nat_dec_eq(v___x_2265_, v___x_2256_);
lean_dec(v___x_2265_);
if (v___x_2271_ == 0)
{
lean_object* v_toCold_2272_; lean_object* v_ref_2273_; lean_object* v_quotContext_2274_; lean_object* v_currMacroScope_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2283_; 
v_toCold_2272_ = lean_ctor_get(v_a_2231_, 0);
v_ref_2273_ = lean_ctor_get(v_a_2231_, 2);
v_quotContext_2274_ = lean_ctor_get(v_toCold_2272_, 8);
v_currMacroScope_2275_ = lean_ctor_get(v_toCold_2272_, 9);
v___x_2276_ = l_Lean_SourceInfo_fromRef(v_ref_2273_, v___x_2271_);
v___x_2277_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__0));
v___x_2278_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__1));
lean_inc_n(v___x_2276_, 2);
v___x_2279_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2276_);
lean_ctor_set(v___x_2279_, 1, v___x_2277_);
v___x_2280_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_2281_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3);
if (v_isShared_2248_ == 0)
{
lean_ctor_set_tag(v___x_2247_, 1);
lean_ctor_set(v___x_2247_, 2, v___x_2281_);
lean_ctor_set(v___x_2247_, 1, v___x_2280_);
lean_ctor_set(v___x_2247_, 0, v___x_2276_);
v___x_2283_ = v___x_2247_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2276_);
lean_ctor_set(v_reuseFailAlloc_2376_, 1, v___x_2280_);
lean_ctor_set(v_reuseFailAlloc_2376_, 2, v___x_2281_);
v___x_2283_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2290_; 
v___x_2284_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__7));
v___x_2285_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__9, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__9_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__9);
v___x_2286_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__10));
lean_inc(v_currMacroScope_2275_);
lean_inc(v_quotContext_2274_);
v___x_2287_ = l_Lean_addMacroScope(v_quotContext_2274_, v___x_2286_, v_currMacroScope_2275_);
v___x_2288_ = lean_box(0);
lean_inc(v___x_2276_);
if (v_isShared_2237_ == 0)
{
lean_ctor_set_tag(v___x_2236_, 3);
lean_ctor_set(v___x_2236_, 3, v___x_2288_);
lean_ctor_set(v___x_2236_, 2, v___x_2287_);
lean_ctor_set(v___x_2236_, 1, v___x_2285_);
lean_ctor_set(v___x_2236_, 0, v___x_2276_);
v___x_2290_ = v___x_2236_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2276_);
lean_ctor_set(v_reuseFailAlloc_2375_, 1, v___x_2285_);
lean_ctor_set(v_reuseFailAlloc_2375_, 2, v___x_2287_);
lean_ctor_set(v_reuseFailAlloc_2375_, 3, v___x_2288_);
v___x_2290_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2373_; 
v___x_2291_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__11));
lean_inc_n(v___x_2276_, 41);
v___x_2292_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2276_);
lean_ctor_set(v___x_2292_, 1, v___x_2291_);
lean_inc_ref(v___x_2290_);
v___x_2293_ = l_Lean_Syntax_node2(v___x_2276_, v___x_2280_, v___x_2290_, v___x_2292_);
v___x_2294_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3));
v___x_2295_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35);
v___x_2296_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__36));
lean_inc_n(v_currMacroScope_2275_, 6);
lean_inc_n(v_quotContext_2274_, 6);
v___x_2297_ = l_Lean_addMacroScope(v_quotContext_2274_, v___x_2296_, v_currMacroScope_2275_);
v___x_2298_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__13));
v___x_2299_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2276_);
lean_ctor_set(v___x_2299_, 1, v___x_2295_);
lean_ctor_set(v___x_2299_, 2, v___x_2297_);
lean_ctor_set(v___x_2299_, 3, v___x_2298_);
v___x_2300_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__16));
v___x_2301_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18));
v___x_2302_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__19));
v___x_2303_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2276_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
v___x_2304_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__21));
v___x_2305_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23);
v___x_2306_ = l_Lean_addMacroScope(v_quotContext_2274_, v___x_2251_, v_currMacroScope_2275_);
v___x_2307_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__16));
v___x_2308_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2276_);
lean_ctor_set(v___x_2308_, 1, v___x_2305_);
lean_ctor_set(v___x_2308_, 2, v___x_2306_);
lean_ctor_set(v___x_2308_, 3, v___x_2307_);
v___x_2309_ = l_Lean_Syntax_node1(v___x_2276_, v___x_2304_, v___x_2308_);
v___x_2310_ = l_Lean_Syntax_node2(v___x_2276_, v___x_2301_, v___x_2303_, v___x_2309_);
v___x_2311_ = l_Lean_mkCIdent(v_ctorIdxName_2259_);
lean_inc(v_x1_2255_);
v___x_2312_ = l_Lean_Syntax_node1(v___x_2276_, v___x_2280_, v_x1_2255_);
lean_inc(v___x_2311_);
v___x_2313_ = l_Lean_Syntax_node2(v___x_2276_, v___x_2294_, v___x_2311_, v___x_2312_);
v___x_2314_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__40));
v___x_2315_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2276_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
lean_inc_ref_n(v___x_2315_, 2);
lean_inc_n(v___x_2310_, 2);
v___x_2316_ = l_Lean_Syntax_node3(v___x_2276_, v___x_2300_, v___x_2310_, v___x_2313_, v___x_2315_);
lean_inc(v_x2_2258_);
v___x_2317_ = l_Lean_Syntax_node1(v___x_2276_, v___x_2280_, v_x2_2258_);
v___x_2318_ = l_Lean_Syntax_node2(v___x_2276_, v___x_2294_, v___x_2311_, v___x_2317_);
v___x_2319_ = l_Lean_Syntax_node3(v___x_2276_, v___x_2300_, v___x_2310_, v___x_2318_, v___x_2315_);
v___x_2320_ = l_Lean_Syntax_node2(v___x_2276_, v___x_2280_, v___x_2316_, v___x_2319_);
v___x_2321_ = l_Lean_Syntax_node2(v___x_2276_, v___x_2294_, v___x_2299_, v___x_2320_);
v___x_2322_ = l_Lean_Syntax_node2(v___x_2276_, v___x_2284_, v___x_2293_, v___x_2321_);
v___x_2323_ = l_Lean_Syntax_node1(v___x_2276_, v___x_2280_, v___x_2322_);
v___x_2324_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__2));
v___x_2325_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2276_);
lean_ctor_set(v___x_2325_, 1, v___x_2324_);
v___x_2326_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__4));
v___x_2327_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__13));
v___x_2328_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__14));
v___x_2329_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2276_);
lean_ctor_set(v___x_2329_, 1, v___x_2328_);
v___x_2330_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__19, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__19_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__19);
v___x_2331_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__21));
v___x_2332_ = l_Lean_addMacroScope(v_quotContext_2274_, v___x_2331_, v_currMacroScope_2275_);
v___x_2333_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__19));
v___x_2334_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2276_);
lean_ctor_set(v___x_2334_, 1, v___x_2330_);
lean_ctor_set(v___x_2334_, 2, v___x_2332_);
lean_ctor_set(v___x_2334_, 3, v___x_2333_);
lean_inc_ref(v___x_2334_);
v___x_2335_ = l_Lean_Syntax_node1(v___x_2276_, v___x_2280_, v___x_2334_);
v___x_2336_ = l_Lean_Syntax_node1(v___x_2276_, v___x_2280_, v___x_2335_);
v___x_2337_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__17));
v___x_2338_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2276_);
lean_ctor_set(v___x_2338_, 1, v___x_2337_);
lean_inc_ref_n(v___x_2338_, 2);
lean_inc_ref_n(v___x_2329_, 2);
v___x_2339_ = l_Lean_Syntax_node4(v___x_2276_, v___x_2327_, v___x_2329_, v___x_2336_, v___x_2338_, v___x_2334_);
v___x_2340_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__27, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__27_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__27);
v___x_2341_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__29));
v___x_2342_ = l_Lean_addMacroScope(v_quotContext_2274_, v___x_2341_, v_currMacroScope_2275_);
v___x_2343_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__22));
v___x_2344_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2276_);
lean_ctor_set(v___x_2344_, 1, v___x_2340_);
lean_ctor_set(v___x_2344_, 2, v___x_2342_);
lean_ctor_set(v___x_2344_, 3, v___x_2343_);
lean_inc_ref(v___x_2344_);
v___x_2345_ = l_Lean_Syntax_node1(v___x_2276_, v___x_2280_, v___x_2344_);
v___x_2346_ = l_Lean_Syntax_node1(v___x_2276_, v___x_2280_, v___x_2345_);
v___x_2347_ = l_Lean_Syntax_node4(v___x_2276_, v___x_2327_, v___x_2329_, v___x_2346_, v___x_2338_, v___x_2344_);
v___x_2348_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__5);
v___x_2349_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__7));
v___x_2350_ = l_Lean_addMacroScope(v_quotContext_2274_, v___x_2349_, v_currMacroScope_2275_);
v___x_2351_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__25));
v___x_2352_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2276_);
lean_ctor_set(v___x_2352_, 1, v___x_2348_);
lean_ctor_set(v___x_2352_, 2, v___x_2350_);
lean_ctor_set(v___x_2352_, 3, v___x_2351_);
v___x_2353_ = l_Lean_Syntax_node1(v___x_2276_, v___x_2280_, v___x_2352_);
v___x_2354_ = l_Lean_Syntax_node1(v___x_2276_, v___x_2280_, v___x_2353_);
v___x_2355_ = l_Lean_mkCIdent(v_a_2263_);
v___x_2356_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__27, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__27_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__27);
v___x_2357_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__31));
v___x_2358_ = l_Lean_addMacroScope(v_quotContext_2274_, v___x_2357_, v_currMacroScope_2275_);
v___x_2359_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__35));
v___x_2360_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2276_);
lean_ctor_set(v___x_2360_, 1, v___x_2356_);
lean_ctor_set(v___x_2360_, 2, v___x_2358_);
lean_ctor_set(v___x_2360_, 3, v___x_2359_);
v___x_2361_ = l_Lean_Syntax_node1(v___x_2276_, v___x_2280_, v___x_2290_);
v___x_2362_ = l_Lean_Syntax_node2(v___x_2276_, v___x_2294_, v___x_2360_, v___x_2361_);
v___x_2363_ = l_Lean_Syntax_node3(v___x_2276_, v___x_2300_, v___x_2310_, v___x_2362_, v___x_2315_);
v___x_2364_ = l_Array_mkArray3___redArg(v_x1_2255_, v_x2_2258_, v___x_2363_);
v___x_2365_ = l_Array_append___redArg(v___x_2364_, v_a_2267_);
lean_dec(v_a_2267_);
v___x_2366_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2276_);
lean_ctor_set(v___x_2366_, 1, v___x_2280_);
lean_ctor_set(v___x_2366_, 2, v___x_2365_);
v___x_2367_ = l_Lean_Syntax_node2(v___x_2276_, v___x_2294_, v___x_2355_, v___x_2366_);
v___x_2368_ = l_Lean_Syntax_node4(v___x_2276_, v___x_2327_, v___x_2329_, v___x_2354_, v___x_2338_, v___x_2367_);
v___x_2369_ = l_Lean_Syntax_node3(v___x_2276_, v___x_2280_, v___x_2339_, v___x_2347_, v___x_2368_);
v___x_2370_ = l_Lean_Syntax_node1(v___x_2276_, v___x_2326_, v___x_2369_);
lean_inc_ref(v___x_2283_);
v___x_2371_ = l_Lean_Syntax_node6(v___x_2276_, v___x_2278_, v___x_2279_, v___x_2283_, v___x_2283_, v___x_2323_, v___x_2325_, v___x_2370_);
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 0, v___x_2371_);
v___x_2373_ = v___x_2269_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2371_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
else
{
lean_object* v_toCold_2377_; lean_object* v_ref_2378_; lean_object* v_quotContext_2379_; lean_object* v_currMacroScope_2380_; uint8_t v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2391_; 
lean_dec(v_ctorIdxName_2259_);
v_toCold_2377_ = lean_ctor_get(v_a_2231_, 0);
v_ref_2378_ = lean_ctor_get(v_a_2231_, 2);
v_quotContext_2379_ = lean_ctor_get(v_toCold_2377_, 8);
v_currMacroScope_2380_ = lean_ctor_get(v_toCold_2377_, 9);
v___x_2381_ = 0;
v___x_2382_ = l_Lean_SourceInfo_fromRef(v_ref_2378_, v___x_2381_);
v___x_2383_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3));
v___x_2384_ = l_Lean_mkCIdent(v_a_2263_);
v___x_2385_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_2386_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__37, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__37_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__37);
v___x_2387_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__38));
lean_inc(v_currMacroScope_2380_);
lean_inc(v_quotContext_2379_);
v___x_2388_ = l_Lean_addMacroScope(v_quotContext_2379_, v___x_2387_, v_currMacroScope_2380_);
v___x_2389_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__40));
lean_inc(v___x_2382_);
if (v_isShared_2237_ == 0)
{
lean_ctor_set_tag(v___x_2236_, 3);
lean_ctor_set(v___x_2236_, 3, v___x_2389_);
lean_ctor_set(v___x_2236_, 2, v___x_2388_);
lean_ctor_set(v___x_2236_, 1, v___x_2386_);
lean_ctor_set(v___x_2236_, 0, v___x_2382_);
v___x_2391_ = v___x_2236_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v___x_2382_);
lean_ctor_set(v_reuseFailAlloc_2401_, 1, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2401_, 2, v___x_2388_);
lean_ctor_set(v_reuseFailAlloc_2401_, 3, v___x_2389_);
v___x_2391_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2395_; 
v___x_2392_ = l_Array_mkArray3___redArg(v_x1_2255_, v_x2_2258_, v___x_2391_);
v___x_2393_ = l_Array_append___redArg(v___x_2392_, v_a_2267_);
lean_dec(v_a_2267_);
lean_inc(v___x_2382_);
if (v_isShared_2248_ == 0)
{
lean_ctor_set_tag(v___x_2247_, 1);
lean_ctor_set(v___x_2247_, 2, v___x_2393_);
lean_ctor_set(v___x_2247_, 1, v___x_2385_);
lean_ctor_set(v___x_2247_, 0, v___x_2382_);
v___x_2395_ = v___x_2247_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v___x_2382_);
lean_ctor_set(v_reuseFailAlloc_2400_, 1, v___x_2385_);
lean_ctor_set(v_reuseFailAlloc_2400_, 2, v___x_2393_);
v___x_2395_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
lean_object* v___x_2396_; lean_object* v___x_2398_; 
v___x_2396_ = l_Lean_Syntax_node2(v___x_2382_, v___x_2383_, v___x_2384_, v___x_2395_);
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 0, v___x_2396_);
v___x_2398_ = v___x_2269_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v___x_2396_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
}
}
}
}
}
}
else
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2410_; 
lean_dec(v___x_2265_);
lean_dec(v_a_2263_);
lean_dec(v_ctorIdxName_2259_);
lean_dec(v_x2_2258_);
lean_dec(v_x1_2255_);
lean_del_object(v___x_2247_);
lean_del_object(v___x_2236_);
v_a_2403_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2405_ = v___x_2266_;
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v___x_2266_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2408_; 
if (v_isShared_2406_ == 0)
{
v___x_2408_ = v___x_2405_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_a_2403_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
}
else
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2418_; 
lean_dec(v_a_2263_);
lean_dec(v_ctorIdxName_2259_);
lean_dec(v_x2_2258_);
lean_dec(v_x1_2255_);
lean_dec_ref(v___f_2252_);
lean_del_object(v___x_2247_);
lean_del_object(v___x_2236_);
lean_dec_ref(v_indVal_2226_);
v_a_2411_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2413_ = v___x_2264_;
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2264_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2416_; 
if (v_isShared_2414_ == 0)
{
v___x_2416_ = v___x_2413_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_a_2411_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
}
else
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
lean_dec(v_ctorIdxName_2259_);
lean_dec(v_x2_2258_);
lean_dec(v_x1_2255_);
lean_dec_ref(v___f_2252_);
lean_del_object(v___x_2247_);
lean_dec(v_name_2245_);
lean_del_object(v___x_2236_);
lean_dec_ref(v_indVal_2226_);
v_a_2419_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2421_ = v___x_2262_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2262_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_a_2419_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___boxed(lean_object* v_header_2434_, lean_object* v_indVal_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew(v_header_2434_, v_indVal_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_);
lean_dec(v_a_2441_);
lean_dec_ref(v_a_2440_);
lean_dec(v_a_2439_);
lean_dec_ref(v_a_2438_);
lean_dec(v_a_2437_);
lean_dec_ref(v_a_2436_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0(lean_object* v_upperBound_2444_, lean_object* v_indVal_2445_, lean_object* v_xs_2446_, lean_object* v_a_2447_, lean_object* v_inst_2448_, lean_object* v_R_2449_, lean_object* v_a_2450_, lean_object* v_b_2451_, lean_object* v_c_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v___x_2460_; 
v___x_2460_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg(v_upperBound_2444_, v_indVal_2445_, v_xs_2446_, v_a_2447_, v_a_2450_, v_b_2451_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___boxed(lean_object* v_upperBound_2461_, lean_object* v_indVal_2462_, lean_object* v_xs_2463_, lean_object* v_a_2464_, lean_object* v_inst_2465_, lean_object* v_R_2466_, lean_object* v_a_2467_, lean_object* v_b_2468_, lean_object* v_c_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0(v_upperBound_2461_, v_indVal_2462_, v_xs_2463_, v_a_2464_, v_inst_2465_, v_R_2466_, v_a_2467_, v_b_2468_, v_c_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec(v___y_2471_);
lean_dec_ref(v___y_2470_);
lean_dec_ref(v_a_2464_);
lean_dec_ref(v_xs_2463_);
lean_dec_ref(v_indVal_2462_);
lean_dec(v_upperBound_2461_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2(lean_object* v_00_u03b1_2478_, lean_object* v_n_2479_, lean_object* v_f_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
lean_object* v___x_2488_; 
v___x_2488_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2___redArg(v_n_2479_, v_f_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2___boxed(lean_object* v_00_u03b1_2489_, lean_object* v_n_2490_, lean_object* v_f_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2(v_00_u03b1_2489_, v_n_2490_, v_f_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v_n_2490_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2(lean_object* v_00_u03b1_2500_, lean_object* v_f_2501_, lean_object* v_n_2502_, lean_object* v_x_2503_, lean_object* v_i_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
lean_object* v___x_2512_; 
v___x_2512_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2___redArg(v_f_2501_, v_n_2502_, v_x_2503_, v_i_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2___boxed(lean_object* v_00_u03b1_2513_, lean_object* v_f_2514_, lean_object* v_n_2515_, lean_object* v_x_2516_, lean_object* v_i_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2(v_00_u03b1_2513_, v_f_2514_, v_n_2515_, v_x_2516_, v_i_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v_n_2515_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch_spec__0(lean_object* v_opts_2526_, lean_object* v_opt_2527_){
_start:
{
lean_object* v_name_2528_; lean_object* v_defValue_2529_; lean_object* v_map_2530_; lean_object* v___x_2531_; 
v_name_2528_ = lean_ctor_get(v_opt_2527_, 0);
v_defValue_2529_ = lean_ctor_get(v_opt_2527_, 1);
v_map_2530_ = lean_ctor_get(v_opts_2526_, 0);
v___x_2531_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2530_, v_name_2528_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_inc(v_defValue_2529_);
return v_defValue_2529_;
}
else
{
lean_object* v_val_2532_; 
v_val_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_val_2532_);
lean_dec_ref_known(v___x_2531_, 1);
if (lean_obj_tag(v_val_2532_) == 3)
{
lean_object* v_v_2533_; 
v_v_2533_ = lean_ctor_get(v_val_2532_, 0);
lean_inc(v_v_2533_);
lean_dec_ref_known(v_val_2532_, 1);
return v_v_2533_;
}
else
{
lean_dec(v_val_2532_);
lean_inc(v_defValue_2529_);
return v_defValue_2529_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch_spec__0___boxed(lean_object* v_opts_2534_, lean_object* v_opt_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch_spec__0(v_opts_2534_, v_opt_2535_);
lean_dec_ref(v_opt_2535_);
lean_dec_ref(v_opts_2534_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch(lean_object* v_header_2537_, lean_object* v_indVal_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_){
_start:
{
lean_object* v_toCold_2546_; lean_object* v_options_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; uint8_t v___x_2551_; 
v_toCold_2546_ = lean_ctor_get(v_a_2543_, 0);
v_options_2547_ = lean_ctor_get(v_toCold_2546_, 2);
v___x_2548_ = l___private_Lean_Elab_Deriving_Ord_0__deriving_ord_linear__construction__threshold;
v___x_2549_ = l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch_spec__0(v_options_2547_, v___x_2548_);
v___x_2550_ = l_Lean_InductiveVal_numCtors(v_indVal_2538_);
v___x_2551_ = lean_nat_dec_le(v___x_2549_, v___x_2550_);
lean_dec(v___x_2550_);
lean_dec(v___x_2549_);
if (v___x_2551_ == 0)
{
lean_object* v___x_2552_; 
v___x_2552_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld(v_header_2537_, v_indVal_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_);
return v___x_2552_;
}
else
{
lean_object* v___x_2553_; 
v___x_2553_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew(v_header_2537_, v_indVal_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_);
return v___x_2553_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch___boxed(lean_object* v_header_2554_, lean_object* v_indVal_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch(v_header_2554_, v_indVal_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_);
lean_dec(v_a_2561_);
lean_dec_ref(v_a_2560_);
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
lean_dec(v_a_2557_);
lean_dec_ref(v_a_2556_);
return v_res_2563_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14(void){
_start:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2602_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__6));
v___x_2603_ = l_String_toRawSubstring_x27(v___x_2602_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction(lean_object* v_ctx_2637_, lean_object* v_i_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_){
_start:
{
lean_object* v_typeInfos_2646_; lean_object* v_auxFunNames_2647_; uint8_t v_usePartial_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v_auxFunName_2651_; lean_object* v_indVal_2652_; lean_object* v___x_2653_; 
v_typeInfos_2646_ = lean_ctor_get(v_ctx_2637_, 1);
v_auxFunNames_2647_ = lean_ctor_get(v_ctx_2637_, 2);
v_usePartial_2648_ = lean_ctor_get_uint8(v_ctx_2637_, sizeof(void*)*3);
v___x_2649_ = lean_box(0);
v___x_2650_ = l_Lean_instInhabitedInductiveVal_default;
v_auxFunName_2651_ = lean_array_get_borrowed(v___x_2649_, v_auxFunNames_2647_, v_i_2638_);
v_indVal_2652_ = lean_array_get_borrowed(v___x_2650_, v_typeInfos_2646_, v_i_2638_);
lean_inc(v_indVal_2652_);
v___x_2653_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader(v_indVal_2652_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2788_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2656_ = v___x_2653_;
v_isShared_2657_ = v_isSharedCheck_2788_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2653_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2788_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v_body_2659_; lean_object* v___y_2660_; lean_object* v___x_2771_; 
lean_inc(v_indVal_2652_);
lean_inc(v_a_2654_);
v___x_2771_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch(v_a_2654_, v_indVal_2652_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_);
if (lean_obj_tag(v___x_2771_) == 0)
{
if (v_usePartial_2648_ == 0)
{
lean_object* v_a_2772_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_a_2772_);
lean_dec_ref_known(v___x_2771_, 1);
v_body_2659_ = v_a_2772_;
v___y_2660_ = v_a_2643_;
goto v___jp_2658_;
}
else
{
lean_object* v_a_2773_; lean_object* v_argNames_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v_a_2773_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_a_2773_);
lean_dec_ref_known(v___x_2771_, 1);
v_argNames_2774_ = lean_ctor_get(v_a_2654_, 1);
v___x_2775_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader___closed__0));
lean_inc_ref(v_argNames_2774_);
v___x_2776_ = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(v_ctx_2637_, v___x_2775_, v_argNames_2774_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v___x_2778_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_a_2777_);
lean_dec_ref_known(v___x_2776_, 1);
v___x_2778_ = l_Lean_Elab_Deriving_mkLet(v_a_2777_, v_a_2773_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_);
lean_dec(v_a_2777_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_a_2779_);
lean_dec_ref_known(v___x_2778_, 1);
v_body_2659_ = v_a_2779_;
v___y_2660_ = v_a_2643_;
goto v___jp_2658_;
}
else
{
lean_del_object(v___x_2656_);
lean_dec(v_a_2654_);
return v___x_2778_;
}
}
else
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2787_; 
lean_dec(v_a_2773_);
lean_del_object(v___x_2656_);
lean_dec(v_a_2654_);
v_a_2780_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2782_ = v___x_2776_;
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2776_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2785_; 
if (v_isShared_2783_ == 0)
{
v___x_2785_ = v___x_2782_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_a_2780_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
}
}
else
{
lean_del_object(v___x_2656_);
lean_dec(v_a_2654_);
return v___x_2771_;
}
v___jp_2658_:
{
if (v_usePartial_2648_ == 0)
{
lean_object* v_toCold_2661_; lean_object* v_binders_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2709_; 
v_toCold_2661_ = lean_ctor_get(v___y_2660_, 0);
v_binders_2662_ = lean_ctor_get(v_a_2654_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v_a_2654_);
if (v_isSharedCheck_2709_ == 0)
{
lean_object* v_unused_2710_; lean_object* v_unused_2711_; lean_object* v_unused_2712_; 
v_unused_2710_ = lean_ctor_get(v_a_2654_, 3);
lean_dec(v_unused_2710_);
v_unused_2711_ = lean_ctor_get(v_a_2654_, 2);
lean_dec(v_unused_2711_);
v_unused_2712_ = lean_ctor_get(v_a_2654_, 1);
lean_dec(v_unused_2712_);
v___x_2664_ = v_a_2654_;
v_isShared_2665_ = v_isSharedCheck_2709_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_binders_2662_);
lean_dec(v_a_2654_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2709_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v_ref_2666_; lean_object* v_quotContext_2667_; lean_object* v_currMacroScope_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2693_; 
v_ref_2666_ = lean_ctor_get(v___y_2660_, 2);
v_quotContext_2667_ = lean_ctor_get(v_toCold_2661_, 8);
v_currMacroScope_2668_ = lean_ctor_get(v_toCold_2661_, 9);
v___x_2669_ = l_Lean_SourceInfo_fromRef(v_ref_2666_, v_usePartial_2648_);
v___x_2670_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__2));
v___x_2671_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__4));
v___x_2672_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_2673_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3);
lean_inc_n(v___x_2669_, 7);
v___x_2674_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2669_);
lean_ctor_set(v___x_2674_, 1, v___x_2672_);
lean_ctor_set(v___x_2674_, 2, v___x_2673_);
lean_inc_ref_n(v___x_2674_, 8);
v___x_2675_ = l_Lean_Syntax_node7(v___x_2669_, v___x_2671_, v___x_2674_, v___x_2674_, v___x_2674_, v___x_2674_, v___x_2674_, v___x_2674_, v___x_2674_);
v___x_2676_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__6));
v___x_2677_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__7));
v___x_2678_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2669_);
lean_ctor_set(v___x_2678_, 1, v___x_2677_);
v___x_2679_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__9));
lean_inc(v_auxFunName_2651_);
v___x_2680_ = l_Lean_mkIdent(v_auxFunName_2651_);
v___x_2681_ = l_Lean_Syntax_node2(v___x_2669_, v___x_2679_, v___x_2680_, v___x_2674_);
v___x_2682_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__11));
v___x_2683_ = l_Array_append___redArg(v___x_2673_, v_binders_2662_);
lean_dec_ref(v_binders_2662_);
v___x_2684_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2669_);
lean_ctor_set(v___x_2684_, 1, v___x_2672_);
lean_ctor_set(v___x_2684_, 2, v___x_2683_);
v___x_2685_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__13));
v___x_2686_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__11));
v___x_2687_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2669_);
lean_ctor_set(v___x_2687_, 1, v___x_2686_);
v___x_2688_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14);
v___x_2689_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__15));
lean_inc(v_currMacroScope_2668_);
lean_inc(v_quotContext_2667_);
v___x_2690_ = l_Lean_addMacroScope(v_quotContext_2667_, v___x_2689_, v_currMacroScope_2668_);
v___x_2691_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__19));
if (v_isShared_2665_ == 0)
{
lean_ctor_set_tag(v___x_2664_, 3);
lean_ctor_set(v___x_2664_, 3, v___x_2691_);
lean_ctor_set(v___x_2664_, 2, v___x_2690_);
lean_ctor_set(v___x_2664_, 1, v___x_2688_);
lean_ctor_set(v___x_2664_, 0, v___x_2669_);
v___x_2693_ = v___x_2664_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v___x_2669_);
lean_ctor_set(v_reuseFailAlloc_2708_, 1, v___x_2688_);
lean_ctor_set(v_reuseFailAlloc_2708_, 2, v___x_2690_);
lean_ctor_set(v_reuseFailAlloc_2708_, 3, v___x_2691_);
v___x_2693_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2706_; 
lean_inc_n(v___x_2669_, 7);
v___x_2694_ = l_Lean_Syntax_node2(v___x_2669_, v___x_2685_, v___x_2687_, v___x_2693_);
v___x_2695_ = l_Lean_Syntax_node1(v___x_2669_, v___x_2672_, v___x_2694_);
v___x_2696_ = l_Lean_Syntax_node2(v___x_2669_, v___x_2682_, v___x_2684_, v___x_2695_);
v___x_2697_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__21));
v___x_2698_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__22));
v___x_2699_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2669_);
lean_ctor_set(v___x_2699_, 1, v___x_2698_);
v___x_2700_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__25));
lean_inc_ref_n(v___x_2674_, 3);
v___x_2701_ = l_Lean_Syntax_node2(v___x_2669_, v___x_2700_, v___x_2674_, v___x_2674_);
v___x_2702_ = l_Lean_Syntax_node4(v___x_2669_, v___x_2697_, v___x_2699_, v_body_2659_, v___x_2701_, v___x_2674_);
v___x_2703_ = l_Lean_Syntax_node5(v___x_2669_, v___x_2676_, v___x_2678_, v___x_2681_, v___x_2696_, v___x_2702_, v___x_2674_);
v___x_2704_ = l_Lean_Syntax_node2(v___x_2669_, v___x_2670_, v___x_2675_, v___x_2703_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 0, v___x_2704_);
v___x_2706_ = v___x_2656_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2704_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
}
else
{
lean_object* v_toCold_2713_; lean_object* v_binders_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2767_; 
v_toCold_2713_ = lean_ctor_get(v___y_2660_, 0);
v_binders_2714_ = lean_ctor_get(v_a_2654_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v_a_2654_);
if (v_isSharedCheck_2767_ == 0)
{
lean_object* v_unused_2768_; lean_object* v_unused_2769_; lean_object* v_unused_2770_; 
v_unused_2768_ = lean_ctor_get(v_a_2654_, 3);
lean_dec(v_unused_2768_);
v_unused_2769_ = lean_ctor_get(v_a_2654_, 2);
lean_dec(v_unused_2769_);
v_unused_2770_ = lean_ctor_get(v_a_2654_, 1);
lean_dec(v_unused_2770_);
v___x_2716_ = v_a_2654_;
v_isShared_2717_ = v_isSharedCheck_2767_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_binders_2714_);
lean_dec(v_a_2654_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2767_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v_ref_2718_; lean_object* v_quotContext_2719_; lean_object* v_currMacroScope_2720_; uint8_t v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2751_; 
v_ref_2718_ = lean_ctor_get(v___y_2660_, 2);
v_quotContext_2719_ = lean_ctor_get(v_toCold_2713_, 8);
v_currMacroScope_2720_ = lean_ctor_get(v_toCold_2713_, 9);
v___x_2721_ = 0;
v___x_2722_ = l_Lean_SourceInfo_fromRef(v_ref_2718_, v___x_2721_);
v___x_2723_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__2));
v___x_2724_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__4));
v___x_2725_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_2726_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3);
lean_inc_n(v___x_2722_, 10);
v___x_2727_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2722_);
lean_ctor_set(v___x_2727_, 1, v___x_2725_);
lean_ctor_set(v___x_2727_, 2, v___x_2726_);
v___x_2728_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__26));
v___x_2729_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__27));
v___x_2730_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2730_, 0, v___x_2722_);
lean_ctor_set(v___x_2730_, 1, v___x_2728_);
v___x_2731_ = l_Lean_Syntax_node1(v___x_2722_, v___x_2729_, v___x_2730_);
v___x_2732_ = l_Lean_Syntax_node1(v___x_2722_, v___x_2725_, v___x_2731_);
lean_inc_ref_n(v___x_2727_, 7);
v___x_2733_ = l_Lean_Syntax_node7(v___x_2722_, v___x_2724_, v___x_2727_, v___x_2727_, v___x_2727_, v___x_2727_, v___x_2727_, v___x_2727_, v___x_2732_);
v___x_2734_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__6));
v___x_2735_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__7));
v___x_2736_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2722_);
lean_ctor_set(v___x_2736_, 1, v___x_2735_);
v___x_2737_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__9));
lean_inc(v_auxFunName_2651_);
v___x_2738_ = l_Lean_mkIdent(v_auxFunName_2651_);
v___x_2739_ = l_Lean_Syntax_node2(v___x_2722_, v___x_2737_, v___x_2738_, v___x_2727_);
v___x_2740_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__11));
v___x_2741_ = l_Array_append___redArg(v___x_2726_, v_binders_2714_);
lean_dec_ref(v_binders_2714_);
v___x_2742_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2722_);
lean_ctor_set(v___x_2742_, 1, v___x_2725_);
lean_ctor_set(v___x_2742_, 2, v___x_2741_);
v___x_2743_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__13));
v___x_2744_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__11));
v___x_2745_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2722_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
v___x_2746_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14);
v___x_2747_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__15));
lean_inc(v_currMacroScope_2720_);
lean_inc(v_quotContext_2719_);
v___x_2748_ = l_Lean_addMacroScope(v_quotContext_2719_, v___x_2747_, v_currMacroScope_2720_);
v___x_2749_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__19));
if (v_isShared_2717_ == 0)
{
lean_ctor_set_tag(v___x_2716_, 3);
lean_ctor_set(v___x_2716_, 3, v___x_2749_);
lean_ctor_set(v___x_2716_, 2, v___x_2748_);
lean_ctor_set(v___x_2716_, 1, v___x_2746_);
lean_ctor_set(v___x_2716_, 0, v___x_2722_);
v___x_2751_ = v___x_2716_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v___x_2722_);
lean_ctor_set(v_reuseFailAlloc_2766_, 1, v___x_2746_);
lean_ctor_set(v_reuseFailAlloc_2766_, 2, v___x_2748_);
lean_ctor_set(v_reuseFailAlloc_2766_, 3, v___x_2749_);
v___x_2751_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2764_; 
lean_inc_n(v___x_2722_, 7);
v___x_2752_ = l_Lean_Syntax_node2(v___x_2722_, v___x_2743_, v___x_2745_, v___x_2751_);
v___x_2753_ = l_Lean_Syntax_node1(v___x_2722_, v___x_2725_, v___x_2752_);
v___x_2754_ = l_Lean_Syntax_node2(v___x_2722_, v___x_2740_, v___x_2742_, v___x_2753_);
v___x_2755_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__21));
v___x_2756_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__22));
v___x_2757_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2722_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
v___x_2758_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__25));
lean_inc_ref_n(v___x_2727_, 3);
v___x_2759_ = l_Lean_Syntax_node2(v___x_2722_, v___x_2758_, v___x_2727_, v___x_2727_);
v___x_2760_ = l_Lean_Syntax_node4(v___x_2722_, v___x_2755_, v___x_2757_, v_body_2659_, v___x_2759_, v___x_2727_);
v___x_2761_ = l_Lean_Syntax_node5(v___x_2722_, v___x_2734_, v___x_2736_, v___x_2739_, v___x_2754_, v___x_2760_, v___x_2727_);
v___x_2762_ = l_Lean_Syntax_node2(v___x_2722_, v___x_2723_, v___x_2733_, v___x_2761_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 0, v___x_2762_);
v___x_2764_ = v___x_2656_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2762_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
v_a_2789_ = lean_ctor_get(v___x_2653_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2791_ = v___x_2653_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2653_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2789_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___boxed(lean_object* v_ctx_2797_, lean_object* v_i_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction(v_ctx_2797_, v_i_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_);
lean_dec(v_a_2804_);
lean_dec_ref(v_a_2803_);
lean_dec(v_a_2802_);
lean_dec_ref(v_a_2801_);
lean_dec(v_a_2800_);
lean_dec_ref(v_a_2799_);
lean_dec(v_i_2798_);
lean_dec_ref(v_ctx_2797_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0___redArg(lean_object* v_upperBound_2807_, lean_object* v_ctx_2808_, lean_object* v_a_2809_, lean_object* v_b_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
uint8_t v___x_2818_; 
v___x_2818_ = lean_nat_dec_lt(v_a_2809_, v_upperBound_2807_);
if (v___x_2818_ == 0)
{
lean_object* v___x_2819_; 
lean_dec(v_a_2809_);
v___x_2819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2819_, 0, v_b_2810_);
return v___x_2819_;
}
else
{
lean_object* v___x_2820_; 
v___x_2820_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction(v_ctx_2808_, v_a_2809_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref_known(v___x_2820_, 1);
v___x_2822_ = lean_array_push(v_b_2810_, v_a_2821_);
v___x_2823_ = lean_unsigned_to_nat(1u);
v___x_2824_ = lean_nat_add(v_a_2809_, v___x_2823_);
lean_dec(v_a_2809_);
v_a_2809_ = v___x_2824_;
v_b_2810_ = v___x_2822_;
goto _start;
}
else
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
lean_dec_ref(v_b_2810_);
lean_dec(v_a_2809_);
v_a_2826_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2820_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2820_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2831_; 
if (v_isShared_2829_ == 0)
{
v___x_2831_ = v___x_2828_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2826_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0___redArg___boxed(lean_object* v_upperBound_2834_, lean_object* v_ctx_2835_, lean_object* v_a_2836_, lean_object* v_b_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v_res_2845_; 
v_res_2845_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0___redArg(v_upperBound_2834_, v_ctx_2835_, v_a_2836_, v_b_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2842_);
lean_dec(v___y_2841_);
lean_dec_ref(v___y_2840_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec_ref(v_ctx_2835_);
lean_dec(v_upperBound_2834_);
return v_res_2845_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__5(void){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2859_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__4));
v___x_2860_ = l_String_toRawSubstring_x27(v___x_2859_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock(lean_object* v_ctx_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_){
_start:
{
lean_object* v_typeInfos_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v_auxDefs_2887_; lean_object* v___x_2888_; 
v_typeInfos_2884_ = lean_ctor_get(v_ctx_2876_, 1);
v___x_2885_ = lean_array_get_size(v_typeInfos_2884_);
v___x_2886_ = lean_unsigned_to_nat(0u);
v_auxDefs_2887_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__2));
v___x_2888_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0___redArg(v___x_2885_, v_ctx_2876_, v___x_2886_, v_auxDefs_2887_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_, v_a_2882_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_object* v_toCold_2889_; lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2925_; 
v_toCold_2889_ = lean_ctor_get(v_a_2881_, 0);
v_a_2890_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2892_ = v___x_2888_;
v_isShared_2893_ = v_isSharedCheck_2925_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2888_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2925_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v_ref_2894_; lean_object* v_quotContext_2895_; lean_object* v_currMacroScope_2896_; uint8_t v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2923_; 
v_ref_2894_ = lean_ctor_get(v_a_2881_, 2);
v_quotContext_2895_ = lean_ctor_get(v_toCold_2889_, 8);
v_currMacroScope_2896_ = lean_ctor_get(v_toCold_2889_, 9);
v___x_2897_ = 0;
v___x_2898_ = l_Lean_SourceInfo_fromRef(v_ref_2894_, v___x_2897_);
v___x_2899_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__0));
v___x_2900_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1));
lean_inc_n(v___x_2898_, 8);
v___x_2901_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2898_);
lean_ctor_set(v___x_2901_, 1, v___x_2899_);
v___x_2902_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_2903_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__2));
v___x_2904_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3));
v___x_2905_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2898_);
lean_ctor_set(v___x_2905_, 1, v___x_2903_);
v___x_2906_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__5, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__5_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__5);
v___x_2907_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__7));
lean_inc(v_currMacroScope_2896_);
lean_inc(v_quotContext_2895_);
v___x_2908_ = l_Lean_addMacroScope(v_quotContext_2895_, v___x_2907_, v_currMacroScope_2896_);
v___x_2909_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__10));
v___x_2910_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2898_);
lean_ctor_set(v___x_2910_, 1, v___x_2906_);
lean_ctor_set(v___x_2910_, 2, v___x_2908_);
lean_ctor_set(v___x_2910_, 3, v___x_2909_);
v___x_2911_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3);
v___x_2912_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2898_);
lean_ctor_set(v___x_2912_, 1, v___x_2902_);
lean_ctor_set(v___x_2912_, 2, v___x_2911_);
v___x_2913_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__11));
v___x_2914_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2898_);
lean_ctor_set(v___x_2914_, 1, v___x_2913_);
v___x_2915_ = l_Lean_Syntax_node4(v___x_2898_, v___x_2904_, v___x_2905_, v___x_2910_, v___x_2912_, v___x_2914_);
v___x_2916_ = l_Array_mkArray1___redArg(v___x_2915_);
v___x_2917_ = l_Array_append___redArg(v___x_2916_, v_a_2890_);
lean_dec(v_a_2890_);
v___x_2918_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2898_);
lean_ctor_set(v___x_2918_, 1, v___x_2902_);
lean_ctor_set(v___x_2918_, 2, v___x_2917_);
v___x_2919_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__12));
v___x_2920_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2898_);
lean_ctor_set(v___x_2920_, 1, v___x_2919_);
v___x_2921_ = l_Lean_Syntax_node3(v___x_2898_, v___x_2900_, v___x_2901_, v___x_2918_, v___x_2920_);
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 0, v___x_2921_);
v___x_2923_ = v___x_2892_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v___x_2921_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
else
{
lean_object* v_a_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_2933_; 
v_a_2926_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2928_ = v___x_2888_;
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_a_2926_);
lean_dec(v___x_2888_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_2933_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2931_; 
if (v_isShared_2929_ == 0)
{
v___x_2931_ = v___x_2928_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___boxed(lean_object* v_ctx_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock(v_ctx_2934_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
lean_dec(v_a_2940_);
lean_dec_ref(v_a_2939_);
lean_dec(v_a_2938_);
lean_dec_ref(v_a_2937_);
lean_dec(v_a_2936_);
lean_dec_ref(v_a_2935_);
lean_dec_ref(v_ctx_2934_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0(lean_object* v_upperBound_2943_, lean_object* v_ctx_2944_, lean_object* v_inst_2945_, lean_object* v_R_2946_, lean_object* v_a_2947_, lean_object* v_b_2948_, lean_object* v_c_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_){
_start:
{
lean_object* v___x_2957_; 
v___x_2957_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0___redArg(v_upperBound_2943_, v_ctx_2944_, v_a_2947_, v_b_2948_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0___boxed(lean_object* v_upperBound_2958_, lean_object* v_ctx_2959_, lean_object* v_inst_2960_, lean_object* v_R_2961_, lean_object* v_a_2962_, lean_object* v_b_2963_, lean_object* v_c_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_){
_start:
{
lean_object* v_res_2972_; 
v_res_2972_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0(v_upperBound_2958_, v_ctx_2959_, v_inst_2960_, v_R_2961_, v_a_2962_, v_b_2963_, v_c_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec_ref(v_ctx_2959_);
lean_dec(v_upperBound_2958_);
return v_res_2972_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2973_; double v___x_2974_; 
v___x_2973_ = lean_unsigned_to_nat(0u);
v___x_2974_ = lean_float_of_nat(v___x_2973_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg(lean_object* v_cls_2977_, lean_object* v_msg_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_){
_start:
{
lean_object* v_ref_2984_; lean_object* v___x_2985_; lean_object* v_a_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_3030_; 
v_ref_2984_ = lean_ctor_get(v___y_2981_, 2);
v___x_2985_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(v_msg_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_);
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_2988_ = v___x_2985_;
v_isShared_2989_ = v_isSharedCheck_3030_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_a_2986_);
lean_dec(v___x_2985_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_3030_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2990_; lean_object* v_traceState_2991_; lean_object* v_env_2992_; lean_object* v_nextMacroScope_2993_; lean_object* v_ngen_2994_; lean_object* v_auxDeclNGen_2995_; lean_object* v_cache_2996_; lean_object* v_messages_2997_; lean_object* v_infoState_2998_; lean_object* v_snapshotTasks_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3029_; 
v___x_2990_ = lean_st_ref_take(v___y_2982_);
v_traceState_2991_ = lean_ctor_get(v___x_2990_, 4);
v_env_2992_ = lean_ctor_get(v___x_2990_, 0);
v_nextMacroScope_2993_ = lean_ctor_get(v___x_2990_, 1);
v_ngen_2994_ = lean_ctor_get(v___x_2990_, 2);
v_auxDeclNGen_2995_ = lean_ctor_get(v___x_2990_, 3);
v_cache_2996_ = lean_ctor_get(v___x_2990_, 5);
v_messages_2997_ = lean_ctor_get(v___x_2990_, 6);
v_infoState_2998_ = lean_ctor_get(v___x_2990_, 7);
v_snapshotTasks_2999_ = lean_ctor_get(v___x_2990_, 8);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3001_ = v___x_2990_;
v_isShared_3002_ = v_isSharedCheck_3029_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_snapshotTasks_2999_);
lean_inc(v_infoState_2998_);
lean_inc(v_messages_2997_);
lean_inc(v_cache_2996_);
lean_inc(v_traceState_2991_);
lean_inc(v_auxDeclNGen_2995_);
lean_inc(v_ngen_2994_);
lean_inc(v_nextMacroScope_2993_);
lean_inc(v_env_2992_);
lean_dec(v___x_2990_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3029_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
uint64_t v_tid_3003_; lean_object* v_traces_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3028_; 
v_tid_3003_ = lean_ctor_get_uint64(v_traceState_2991_, sizeof(void*)*1);
v_traces_3004_ = lean_ctor_get(v_traceState_2991_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v_traceState_2991_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3006_ = v_traceState_2991_;
v_isShared_3007_ = v_isSharedCheck_3028_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_traces_3004_);
lean_dec(v_traceState_2991_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3028_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; double v___x_3010_; uint8_t v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3019_; 
v___x_3008_ = lean_box(0);
v___x_3009_ = lean_box(0);
v___x_3010_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___closed__0);
v___x_3011_ = 0;
v___x_3012_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__22));
v___x_3013_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3013_, 0, v_cls_2977_);
lean_ctor_set(v___x_3013_, 1, v___x_3009_);
lean_ctor_set(v___x_3013_, 2, v___x_3012_);
lean_ctor_set_float(v___x_3013_, sizeof(void*)*3, v___x_3010_);
lean_ctor_set_float(v___x_3013_, sizeof(void*)*3 + 8, v___x_3010_);
lean_ctor_set_uint8(v___x_3013_, sizeof(void*)*3 + 16, v___x_3011_);
v___x_3014_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___closed__1));
v___x_3015_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3013_);
lean_ctor_set(v___x_3015_, 1, v_a_2986_);
lean_ctor_set(v___x_3015_, 2, v___x_3014_);
lean_inc(v_ref_2984_);
v___x_3016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3016_, 0, v_ref_2984_);
lean_ctor_set(v___x_3016_, 1, v___x_3015_);
v___x_3017_ = l_Lean_PersistentArray_push___redArg(v_traces_3004_, v___x_3016_);
if (v_isShared_3007_ == 0)
{
lean_ctor_set(v___x_3006_, 0, v___x_3017_);
v___x_3019_ = v___x_3006_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v___x_3017_);
lean_ctor_set_uint64(v_reuseFailAlloc_3027_, sizeof(void*)*1, v_tid_3003_);
v___x_3019_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
lean_object* v___x_3021_; 
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 4, v___x_3019_);
v___x_3021_ = v___x_3001_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_env_2992_);
lean_ctor_set(v_reuseFailAlloc_3026_, 1, v_nextMacroScope_2993_);
lean_ctor_set(v_reuseFailAlloc_3026_, 2, v_ngen_2994_);
lean_ctor_set(v_reuseFailAlloc_3026_, 3, v_auxDeclNGen_2995_);
lean_ctor_set(v_reuseFailAlloc_3026_, 4, v___x_3019_);
lean_ctor_set(v_reuseFailAlloc_3026_, 5, v_cache_2996_);
lean_ctor_set(v_reuseFailAlloc_3026_, 6, v_messages_2997_);
lean_ctor_set(v_reuseFailAlloc_3026_, 7, v_infoState_2998_);
lean_ctor_set(v_reuseFailAlloc_3026_, 8, v_snapshotTasks_2999_);
v___x_3021_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
lean_object* v___x_3022_; lean_object* v___x_3024_; 
v___x_3022_ = lean_st_ref_put(v___y_2982_, v___x_3021_);
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 0, v___x_3008_);
v___x_3024_ = v___x_2988_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v___x_3008_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___boxed(lean_object* v_cls_3031_, lean_object* v_msg_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg(v_cls_3031_, v_msg_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec(v___y_3034_);
lean_dec_ref(v___y_3033_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__0(lean_object* v_a_3039_, lean_object* v_a_3040_){
_start:
{
if (lean_obj_tag(v_a_3039_) == 0)
{
lean_object* v___x_3041_; 
v___x_3041_ = l_List_reverse___redArg(v_a_3040_);
return v___x_3041_;
}
else
{
lean_object* v_head_3042_; lean_object* v_tail_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3052_; 
v_head_3042_ = lean_ctor_get(v_a_3039_, 0);
v_tail_3043_ = lean_ctor_get(v_a_3039_, 1);
v_isSharedCheck_3052_ = !lean_is_exclusive(v_a_3039_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3045_ = v_a_3039_;
v_isShared_3046_ = v_isSharedCheck_3052_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_tail_3043_);
lean_inc(v_head_3042_);
lean_dec(v_a_3039_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3052_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3047_; lean_object* v___x_3049_; 
v___x_3047_ = l_Lean_MessageData_ofSyntax(v_head_3042_);
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 1, v_a_3040_);
lean_ctor_set(v___x_3045_, 0, v___x_3047_);
v___x_3049_ = v___x_3045_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3047_);
lean_ctor_set(v_reuseFailAlloc_3051_, 1, v_a_3040_);
v___x_3049_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
v_a_3039_ = v_tail_3043_;
v_a_3040_ = v___x_3049_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3(void){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; 
v___x_3060_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__0));
v___x_3061_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__2));
v___x_3062_ = l_Lean_Name_append(v___x_3061_, v___x_3060_);
return v___x_3062_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5(void){
_start:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___x_3064_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__4));
v___x_3065_ = l_Lean_stringToMessageData(v___x_3064_);
return v___x_3065_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__17(void){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3093_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__16));
v___x_3094_ = l_String_toRawSubstring_x27(v___x_3093_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds(lean_object* v_declName_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_, lean_object* v_a_3102_, lean_object* v_a_3103_, lean_object* v_a_3104_){
_start:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v_cmds_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v_options_3113_; lean_object* v_inheritedTraceOptions_3114_; lean_object* v___y_3115_; uint8_t v___x_3145_; lean_object* v___x_3146_; 
v___x_3106_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader___closed__0));
v___x_3107_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__1_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_));
v___x_3145_ = 0;
lean_inc(v_declName_3098_);
v___x_3146_ = l_Lean_Elab_Deriving_mkContext(v___x_3106_, v___x_3107_, v_declName_3098_, v___x_3145_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v_a_3147_; lean_object* v___x_3148_; 
v_a_3147_ = lean_ctor_get(v___x_3146_, 0);
lean_inc(v_a_3147_);
lean_dec_ref_known(v___x_3146_, 1);
v___x_3148_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock(v_a_3147_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_);
if (lean_obj_tag(v___x_3148_) == 0)
{
lean_object* v_a_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; uint8_t v___x_3153_; lean_object* v___x_3154_; 
v_a_3149_ = lean_ctor_get(v___x_3148_, 0);
lean_inc(v_a_3149_);
lean_dec_ref_known(v___x_3148_, 1);
v___x_3150_ = lean_unsigned_to_nat(1u);
v___x_3151_ = lean_mk_empty_array_with_capacity(v___x_3150_);
lean_inc_ref(v___x_3151_);
v___x_3152_ = lean_array_push(v___x_3151_, v_declName_3098_);
v___x_3153_ = 1;
lean_inc(v_a_3147_);
v___x_3154_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_a_3147_, v___x_3106_, v___x_3152_, v___x_3153_, v_a_3099_, v_a_3100_, v_a_3101_, v_a_3102_, v_a_3103_, v_a_3104_);
lean_dec_ref(v___x_3152_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v_a_3155_; lean_object* v_instName_3156_; uint8_t v_usePartial_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
lean_inc(v_a_3155_);
lean_dec_ref_known(v___x_3154_, 1);
v_instName_3156_ = lean_ctor_get(v_a_3147_, 0);
lean_inc(v_instName_3156_);
v_usePartial_3157_ = lean_ctor_get_uint8(v_a_3147_, sizeof(void*)*3);
lean_dec(v_a_3147_);
v___x_3158_ = lean_array_push(v___x_3151_, v_a_3149_);
v___x_3159_ = l_Array_append___redArg(v___x_3158_, v_a_3155_);
lean_dec(v_a_3155_);
if (v_usePartial_3157_ == 0)
{
lean_object* v_toCold_3160_; lean_object* v_ref_3161_; lean_object* v_options_3162_; lean_object* v_quotContext_3163_; lean_object* v_currMacroScope_3164_; lean_object* v_inheritedTraceOptions_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v_toCold_3160_ = lean_ctor_get(v_a_3103_, 0);
v_ref_3161_ = lean_ctor_get(v_a_3103_, 2);
v_options_3162_ = lean_ctor_get(v_toCold_3160_, 2);
v_quotContext_3163_ = lean_ctor_get(v_toCold_3160_, 8);
v_currMacroScope_3164_ = lean_ctor_get(v_toCold_3160_, 9);
v_inheritedTraceOptions_3165_ = lean_ctor_get(v_toCold_3160_, 11);
v___x_3166_ = l_Lean_SourceInfo_fromRef(v_ref_3161_, v_usePartial_3157_);
v___x_3167_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__6));
v___x_3168_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__7));
lean_inc_n(v___x_3166_, 10);
v___x_3169_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3166_);
lean_ctor_set(v___x_3169_, 1, v___x_3167_);
v___x_3170_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__8));
v___x_3171_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3166_);
lean_ctor_set(v___x_3171_, 1, v___x_3170_);
v___x_3172_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_3173_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__10));
v___x_3174_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__12));
v___x_3175_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3);
v___x_3176_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3166_);
lean_ctor_set(v___x_3176_, 1, v___x_3172_);
lean_ctor_set(v___x_3176_, 2, v___x_3175_);
lean_inc_ref(v___x_3176_);
v___x_3177_ = l_Lean_Syntax_node1(v___x_3166_, v___x_3174_, v___x_3176_);
v___x_3178_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__15));
v___x_3179_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__17, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__17_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__17);
v___x_3180_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__18));
lean_inc(v_currMacroScope_3164_);
lean_inc(v_quotContext_3163_);
v___x_3181_ = l_Lean_addMacroScope(v_quotContext_3163_, v___x_3180_, v_currMacroScope_3164_);
v___x_3182_ = lean_box(0);
v___x_3183_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3166_);
lean_ctor_set(v___x_3183_, 1, v___x_3179_);
lean_ctor_set(v___x_3183_, 2, v___x_3181_);
lean_ctor_set(v___x_3183_, 3, v___x_3182_);
v___x_3184_ = l_Lean_Syntax_node2(v___x_3166_, v___x_3178_, v___x_3183_, v___x_3176_);
v___x_3185_ = l_Lean_Syntax_node2(v___x_3166_, v___x_3173_, v___x_3177_, v___x_3184_);
v___x_3186_ = l_Lean_Syntax_node1(v___x_3166_, v___x_3172_, v___x_3185_);
v___x_3187_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__19));
v___x_3188_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3188_, 0, v___x_3166_);
lean_ctor_set(v___x_3188_, 1, v___x_3187_);
v___x_3189_ = l_Lean_mkIdent(v_instName_3156_);
v___x_3190_ = l_Lean_Syntax_node1(v___x_3166_, v___x_3172_, v___x_3189_);
v___x_3191_ = l_Lean_Syntax_node5(v___x_3166_, v___x_3168_, v___x_3169_, v___x_3171_, v___x_3186_, v___x_3188_, v___x_3190_);
v___x_3192_ = lean_array_push(v___x_3159_, v___x_3191_);
lean_inc_ref(v_inheritedTraceOptions_3165_);
lean_inc_ref(v_options_3162_);
v_cmds_3109_ = v___x_3192_;
v___y_3110_ = v_a_3101_;
v___y_3111_ = v_a_3102_;
v___y_3112_ = v_a_3103_;
v_options_3113_ = v_options_3162_;
v_inheritedTraceOptions_3114_ = v_inheritedTraceOptions_3165_;
v___y_3115_ = v_a_3104_;
goto v___jp_3108_;
}
else
{
lean_object* v_toCold_3193_; lean_object* v_options_3194_; lean_object* v_inheritedTraceOptions_3195_; 
lean_dec(v_instName_3156_);
v_toCold_3193_ = lean_ctor_get(v_a_3103_, 0);
v_options_3194_ = lean_ctor_get(v_toCold_3193_, 2);
v_inheritedTraceOptions_3195_ = lean_ctor_get(v_toCold_3193_, 11);
lean_inc_ref(v_inheritedTraceOptions_3195_);
lean_inc_ref(v_options_3194_);
v_cmds_3109_ = v___x_3159_;
v___y_3110_ = v_a_3101_;
v___y_3111_ = v_a_3102_;
v___y_3112_ = v_a_3103_;
v_options_3113_ = v_options_3194_;
v_inheritedTraceOptions_3114_ = v_inheritedTraceOptions_3195_;
v___y_3115_ = v_a_3104_;
goto v___jp_3108_;
}
}
else
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3203_; 
lean_dec_ref(v___x_3151_);
lean_dec(v_a_3149_);
lean_dec(v_a_3147_);
v_a_3196_ = lean_ctor_get(v___x_3154_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3198_ = v___x_3154_;
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_3154_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3201_; 
if (v_isShared_3199_ == 0)
{
v___x_3201_ = v___x_3198_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_a_3196_);
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
else
{
lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3211_; 
lean_dec(v_a_3147_);
lean_dec(v_declName_3098_);
v_a_3204_ = lean_ctor_get(v___x_3148_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3148_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3206_ = v___x_3148_;
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_3148_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3209_; 
if (v_isShared_3207_ == 0)
{
v___x_3209_ = v___x_3206_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_a_3204_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
}
else
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3219_; 
lean_dec(v_declName_3098_);
v_a_3212_ = lean_ctor_get(v___x_3146_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3214_ = v___x_3146_;
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_3146_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3217_; 
if (v_isShared_3215_ == 0)
{
v___x_3217_ = v___x_3214_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_a_3212_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
}
}
}
v___jp_3108_:
{
uint8_t v_hasTrace_3116_; 
v_hasTrace_3116_ = lean_ctor_get_uint8(v_options_3113_, sizeof(void*)*1);
if (v_hasTrace_3116_ == 0)
{
lean_object* v___x_3117_; 
lean_dec_ref(v_inheritedTraceOptions_3114_);
lean_dec_ref(v_options_3113_);
v___x_3117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3117_, 0, v_cmds_3109_);
return v___x_3117_;
}
else
{
lean_object* v___x_3118_; lean_object* v___x_3119_; uint8_t v___x_3120_; 
v___x_3118_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__0));
v___x_3119_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3);
v___x_3120_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3114_, v_options_3113_, v___x_3119_);
lean_dec_ref(v_options_3113_);
lean_dec_ref(v_inheritedTraceOptions_3114_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3121_; 
v___x_3121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3121_, 0, v_cmds_3109_);
return v___x_3121_;
}
else
{
lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3122_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5);
lean_inc_ref(v_cmds_3109_);
v___x_3123_ = lean_array_to_list(v_cmds_3109_);
v___x_3124_ = lean_box(0);
v___x_3125_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__0(v___x_3123_, v___x_3124_);
v___x_3126_ = l_Lean_MessageData_ofList(v___x_3125_);
v___x_3127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3122_);
lean_ctor_set(v___x_3127_, 1, v___x_3126_);
v___x_3128_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg(v___x_3118_, v___x_3127_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3115_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3135_; 
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3135_ == 0)
{
lean_object* v_unused_3136_; 
v_unused_3136_ = lean_ctor_get(v___x_3128_, 0);
lean_dec(v_unused_3136_);
v___x_3130_ = v___x_3128_;
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
else
{
lean_dec(v___x_3128_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3133_; 
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 0, v_cmds_3109_);
v___x_3133_ = v___x_3130_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_cmds_3109_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
else
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3144_; 
lean_dec_ref(v_cmds_3109_);
v_a_3137_ = lean_ctor_get(v___x_3128_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3139_ = v___x_3128_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3128_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3142_; 
if (v_isShared_3140_ == 0)
{
v___x_3142_ = v___x_3139_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3137_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___boxed(lean_object* v_declName_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_){
_start:
{
lean_object* v_res_3228_; 
v_res_3228_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds(v_declName_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_);
lean_dec(v_a_3226_);
lean_dec_ref(v_a_3225_);
lean_dec(v_a_3224_);
lean_dec_ref(v_a_3223_);
lean_dec(v_a_3222_);
lean_dec_ref(v_a_3221_);
return v_res_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1(lean_object* v_cls_3229_, lean_object* v_msg_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_){
_start:
{
lean_object* v___x_3238_; 
v___x_3238_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg(v_cls_3229_, v_msg_3230_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___boxed(lean_object* v_cls_3239_, lean_object* v_msg_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
lean_object* v_res_3248_; 
v_res_3248_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1(v_cls_3239_, v_msg_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
return v_res_3248_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__3(void){
_start:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3256_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__2));
v___x_3257_ = l_String_toRawSubstring_x27(v___x_3256_);
return v___x_3257_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__6(void){
_start:
{
lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3261_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__5));
v___x_3262_ = l_String_toRawSubstring_x27(v___x_3261_);
return v___x_3262_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__12(void){
_start:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; 
v___x_3275_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__11));
v___x_3276_ = l_String_toRawSubstring_x27(v___x_3275_);
return v___x_3276_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__16(void){
_start:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3282_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__15));
v___x_3283_ = l_String_toRawSubstring_x27(v___x_3282_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg(lean_object* v_ctx_3287_, lean_object* v_name_3288_, lean_object* v_a_3289_){
_start:
{
lean_object* v_toCold_3291_; lean_object* v_auxFunNames_3292_; lean_object* v_ref_3293_; lean_object* v_quotContext_3294_; lean_object* v_currMacroScope_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v_auxFunName_3298_; uint8_t v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; 
v_toCold_3291_ = lean_ctor_get(v_a_3289_, 0);
v_auxFunNames_3292_ = lean_ctor_get(v_ctx_3287_, 2);
v_ref_3293_ = lean_ctor_get(v_a_3289_, 2);
v_quotContext_3294_ = lean_ctor_get(v_toCold_3291_, 8);
v_currMacroScope_3295_ = lean_ctor_get(v_toCold_3291_, 9);
v___x_3296_ = lean_box(0);
v___x_3297_ = lean_unsigned_to_nat(0u);
v_auxFunName_3298_ = lean_array_get_borrowed(v___x_3296_, v_auxFunNames_3292_, v___x_3297_);
v___x_3299_ = 0;
v___x_3300_ = l_Lean_SourceInfo_fromRef(v_ref_3293_, v___x_3299_);
v___x_3301_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__2));
v___x_3302_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__4));
v___x_3303_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_3304_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3);
lean_inc_n(v___x_3300_, 26);
v___x_3305_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3300_);
lean_ctor_set(v___x_3305_, 1, v___x_3303_);
lean_ctor_set(v___x_3305_, 2, v___x_3304_);
lean_inc_ref_n(v___x_3305_, 12);
v___x_3306_ = l_Lean_Syntax_node7(v___x_3300_, v___x_3302_, v___x_3305_, v___x_3305_, v___x_3305_, v___x_3305_, v___x_3305_, v___x_3305_, v___x_3305_);
v___x_3307_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__6));
v___x_3308_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__7));
v___x_3309_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3300_);
lean_ctor_set(v___x_3309_, 1, v___x_3308_);
v___x_3310_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__9));
lean_inc(v_auxFunName_3298_);
v___x_3311_ = l_Lean_mkIdent(v_auxFunName_3298_);
v___x_3312_ = l_Lean_Syntax_node2(v___x_3300_, v___x_3310_, v___x_3311_, v___x_3305_);
v___x_3313_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__11));
v___x_3314_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__1));
v___x_3315_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__19));
v___x_3316_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3300_);
lean_ctor_set(v___x_3316_, 1, v___x_3315_);
v___x_3317_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__3, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__3_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__3);
v___x_3318_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__4));
lean_inc_n(v_currMacroScope_3295_, 6);
lean_inc_n(v_quotContext_3294_, 6);
v___x_3319_ = l_Lean_addMacroScope(v_quotContext_3294_, v___x_3318_, v_currMacroScope_3295_);
v___x_3320_ = lean_box(0);
v___x_3321_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3300_);
lean_ctor_set(v___x_3321_, 1, v___x_3317_);
lean_ctor_set(v___x_3321_, 2, v___x_3319_);
lean_ctor_set(v___x_3321_, 3, v___x_3320_);
v___x_3322_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__6, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__6_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__6);
v___x_3323_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__7));
v___x_3324_ = l_Lean_addMacroScope(v_quotContext_3294_, v___x_3323_, v_currMacroScope_3295_);
v___x_3325_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3300_);
lean_ctor_set(v___x_3325_, 1, v___x_3322_);
lean_ctor_set(v___x_3325_, 2, v___x_3324_);
lean_ctor_set(v___x_3325_, 3, v___x_3320_);
v___x_3326_ = l_Lean_Syntax_node2(v___x_3300_, v___x_3303_, v___x_3321_, v___x_3325_);
v___x_3327_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__11));
v___x_3328_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3300_);
lean_ctor_set(v___x_3328_, 1, v___x_3327_);
v___x_3329_ = l_Lean_mkCIdent(v_name_3288_);
lean_inc_ref(v___x_3328_);
v___x_3330_ = l_Lean_Syntax_node2(v___x_3300_, v___x_3303_, v___x_3328_, v___x_3329_);
v___x_3331_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__40));
v___x_3332_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3300_);
lean_ctor_set(v___x_3332_, 1, v___x_3331_);
v___x_3333_ = l_Lean_Syntax_node5(v___x_3300_, v___x_3314_, v___x_3316_, v___x_3326_, v___x_3330_, v___x_3305_, v___x_3332_);
v___x_3334_ = l_Lean_Syntax_node1(v___x_3300_, v___x_3303_, v___x_3333_);
v___x_3335_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__13));
v___x_3336_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14);
v___x_3337_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__15));
v___x_3338_ = l_Lean_addMacroScope(v_quotContext_3294_, v___x_3337_, v_currMacroScope_3295_);
v___x_3339_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__10));
v___x_3340_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3340_, 0, v___x_3300_);
lean_ctor_set(v___x_3340_, 1, v___x_3336_);
lean_ctor_set(v___x_3340_, 2, v___x_3338_);
lean_ctor_set(v___x_3340_, 3, v___x_3339_);
v___x_3341_ = l_Lean_Syntax_node2(v___x_3300_, v___x_3335_, v___x_3328_, v___x_3340_);
v___x_3342_ = l_Lean_Syntax_node1(v___x_3300_, v___x_3303_, v___x_3341_);
v___x_3343_ = l_Lean_Syntax_node2(v___x_3300_, v___x_3313_, v___x_3334_, v___x_3342_);
v___x_3344_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__21));
v___x_3345_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__22));
v___x_3346_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3300_);
lean_ctor_set(v___x_3346_, 1, v___x_3345_);
v___x_3347_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3));
v___x_3348_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35);
v___x_3349_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__36));
v___x_3350_ = l_Lean_addMacroScope(v_quotContext_3294_, v___x_3349_, v_currMacroScope_3295_);
v___x_3351_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__13));
v___x_3352_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3300_);
lean_ctor_set(v___x_3352_, 1, v___x_3348_);
lean_ctor_set(v___x_3352_, 2, v___x_3350_);
lean_ctor_set(v___x_3352_, 3, v___x_3351_);
v___x_3353_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__12, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__12_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__12);
v___x_3354_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__14));
v___x_3355_ = l_Lean_addMacroScope(v_quotContext_3294_, v___x_3354_, v_currMacroScope_3295_);
v___x_3356_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3300_);
lean_ctor_set(v___x_3356_, 1, v___x_3353_);
lean_ctor_set(v___x_3356_, 2, v___x_3355_);
lean_ctor_set(v___x_3356_, 3, v___x_3320_);
v___x_3357_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__16, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__16_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__16);
v___x_3358_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__17));
v___x_3359_ = l_Lean_addMacroScope(v_quotContext_3294_, v___x_3358_, v_currMacroScope_3295_);
v___x_3360_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3300_);
lean_ctor_set(v___x_3360_, 1, v___x_3357_);
lean_ctor_set(v___x_3360_, 2, v___x_3359_);
lean_ctor_set(v___x_3360_, 3, v___x_3320_);
v___x_3361_ = l_Lean_Syntax_node2(v___x_3300_, v___x_3303_, v___x_3356_, v___x_3360_);
v___x_3362_ = l_Lean_Syntax_node2(v___x_3300_, v___x_3347_, v___x_3352_, v___x_3361_);
v___x_3363_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__25));
v___x_3364_ = l_Lean_Syntax_node2(v___x_3300_, v___x_3363_, v___x_3305_, v___x_3305_);
v___x_3365_ = l_Lean_Syntax_node4(v___x_3300_, v___x_3344_, v___x_3346_, v___x_3362_, v___x_3364_, v___x_3305_);
v___x_3366_ = l_Lean_Syntax_node5(v___x_3300_, v___x_3307_, v___x_3309_, v___x_3312_, v___x_3343_, v___x_3365_, v___x_3305_);
v___x_3367_ = l_Lean_Syntax_node2(v___x_3300_, v___x_3301_, v___x_3306_, v___x_3366_);
v___x_3368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3367_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___boxed(lean_object* v_ctx_3369_, lean_object* v_name_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_){
_start:
{
lean_object* v_res_3373_; 
v_res_3373_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg(v_ctx_3369_, v_name_3370_, v_a_3371_);
lean_dec_ref(v_a_3371_);
lean_dec_ref(v_ctx_3369_);
return v_res_3373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun(lean_object* v_ctx_3374_, lean_object* v_name_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_){
_start:
{
lean_object* v___x_3383_; 
v___x_3383_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg(v_ctx_3374_, v_name_3375_, v_a_3380_);
return v___x_3383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___boxed(lean_object* v_ctx_3384_, lean_object* v_name_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_){
_start:
{
lean_object* v_res_3393_; 
v_res_3393_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun(v_ctx_3384_, v_name_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_);
lean_dec(v_a_3391_);
lean_dec_ref(v_a_3390_);
lean_dec(v_a_3389_);
lean_dec_ref(v_a_3388_);
lean_dec(v_a_3387_);
lean_dec_ref(v_a_3386_);
lean_dec_ref(v_ctx_3384_);
return v_res_3393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumCmd(lean_object* v_name_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_){
_start:
{
lean_object* v___x_3402_; lean_object* v___x_3403_; uint8_t v___x_3404_; lean_object* v___x_3405_; 
v___x_3402_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader___closed__0));
v___x_3403_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__1_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_));
v___x_3404_ = 1;
lean_inc(v_name_3394_);
v___x_3405_ = l_Lean_Elab_Deriving_mkContext(v___x_3402_, v___x_3403_, v_name_3394_, v___x_3404_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; lean_object* v___x_3407_; lean_object* v_a_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3406_);
lean_dec_ref_known(v___x_3405_, 1);
lean_inc(v_name_3394_);
v___x_3407_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg(v_a_3406_, v_name_3394_, v_a_3399_);
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
lean_inc(v_a_3408_);
lean_dec_ref(v___x_3407_);
v___x_3409_ = lean_unsigned_to_nat(1u);
v___x_3410_ = lean_mk_empty_array_with_capacity(v___x_3409_);
lean_inc_ref(v___x_3410_);
v___x_3411_ = lean_array_push(v___x_3410_, v_name_3394_);
v___x_3412_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_a_3406_, v___x_3402_, v___x_3411_, v___x_3404_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_);
lean_dec_ref(v___x_3411_);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_object* v_toCold_3413_; lean_object* v_options_3414_; lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3455_; 
v_toCold_3413_ = lean_ctor_get(v_a_3399_, 0);
v_options_3414_ = lean_ctor_get(v_toCold_3413_, 2);
v_a_3415_ = lean_ctor_get(v___x_3412_, 0);
v_isSharedCheck_3455_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3455_ == 0)
{
v___x_3417_ = v___x_3412_;
v_isShared_3418_ = v_isSharedCheck_3455_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3412_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3455_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v_inheritedTraceOptions_3419_; uint8_t v_hasTrace_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v_inheritedTraceOptions_3419_ = lean_ctor_get(v_toCold_3413_, 11);
v_hasTrace_3420_ = lean_ctor_get_uint8(v_options_3414_, sizeof(void*)*1);
v___x_3421_ = lean_array_push(v___x_3410_, v_a_3408_);
v___x_3422_ = l_Array_append___redArg(v___x_3421_, v_a_3415_);
lean_dec(v_a_3415_);
if (v_hasTrace_3420_ == 0)
{
lean_object* v___x_3424_; 
if (v_isShared_3418_ == 0)
{
lean_ctor_set(v___x_3417_, 0, v___x_3422_);
v___x_3424_ = v___x_3417_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v___x_3422_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
else
{
lean_object* v___x_3426_; lean_object* v___x_3427_; uint8_t v___x_3428_; 
v___x_3426_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__0));
v___x_3427_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3);
v___x_3428_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3419_, v_options_3414_, v___x_3427_);
if (v___x_3428_ == 0)
{
lean_object* v___x_3430_; 
if (v_isShared_3418_ == 0)
{
lean_ctor_set(v___x_3417_, 0, v___x_3422_);
v___x_3430_ = v___x_3417_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3422_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
else
{
lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
lean_del_object(v___x_3417_);
v___x_3432_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5);
lean_inc_ref(v___x_3422_);
v___x_3433_ = lean_array_to_list(v___x_3422_);
v___x_3434_ = lean_box(0);
v___x_3435_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__0(v___x_3433_, v___x_3434_);
v___x_3436_ = l_Lean_MessageData_ofList(v___x_3435_);
v___x_3437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3432_);
lean_ctor_set(v___x_3437_, 1, v___x_3436_);
v___x_3438_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg(v___x_3426_, v___x_3437_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3445_; 
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3445_ == 0)
{
lean_object* v_unused_3446_; 
v_unused_3446_ = lean_ctor_get(v___x_3438_, 0);
lean_dec(v_unused_3446_);
v___x_3440_ = v___x_3438_;
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
else
{
lean_dec(v___x_3438_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3443_; 
if (v_isShared_3441_ == 0)
{
lean_ctor_set(v___x_3440_, 0, v___x_3422_);
v___x_3443_ = v___x_3440_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3422_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
else
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
lean_dec_ref(v___x_3422_);
v_a_3447_ = lean_ctor_get(v___x_3438_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3449_ = v___x_3438_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3438_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3447_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3463_; 
lean_dec_ref(v___x_3410_);
lean_dec(v_a_3408_);
v_a_3456_ = lean_ctor_get(v___x_3412_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3458_ = v___x_3412_;
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3412_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3461_; 
if (v_isShared_3459_ == 0)
{
v___x_3461_ = v___x_3458_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_a_3456_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
}
else
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
lean_dec(v_name_3394_);
v_a_3464_ = lean_ctor_get(v___x_3405_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3405_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3466_ = v___x_3405_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3405_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3464_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumCmd___boxed(lean_object* v_name_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_){
_start:
{
lean_object* v_res_3480_; 
v_res_3480_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumCmd(v_name_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_);
lean_dec(v_a_3478_);
lean_dec_ref(v_a_3477_);
lean_dec(v_a_3476_);
lean_dec_ref(v_a_3475_);
lean_dec(v_a_3474_);
lean_dec_ref(v_a_3473_);
return v_res_3480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__0(uint8_t v_a_3481_, lean_object* v_declName_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_){
_start:
{
if (v_a_3481_ == 0)
{
lean_object* v___x_3490_; 
v___x_3490_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds(v_declName_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_);
return v___x_3490_;
}
else
{
lean_object* v___x_3491_; 
v___x_3491_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumCmd(v_declName_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_);
return v___x_3491_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__0___boxed(lean_object* v_a_3492_, lean_object* v_declName_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_){
_start:
{
uint8_t v_a_3807__boxed_3501_; lean_object* v_res_3502_; 
v_a_3807__boxed_3501_ = lean_unbox(v_a_3492_);
v_res_3502_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__0(v_a_3807__boxed_3501_, v_declName_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_);
lean_dec(v___y_3499_);
lean_dec_ref(v___y_3498_);
lean_dec(v___y_3497_);
lean_dec_ref(v___y_3496_);
lean_dec(v___y_3495_);
lean_dec_ref(v___y_3494_);
return v_res_3502_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_3503_; 
v___x_3503_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_3503_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3504_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__0);
v___x_3505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3504_);
return v___x_3505_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3506_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1);
v___x_3507_ = lean_unsigned_to_nat(0u);
v___x_3508_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3508_, 0, v___x_3507_);
lean_ctor_set(v___x_3508_, 1, v___x_3507_);
lean_ctor_set(v___x_3508_, 2, v___x_3507_);
lean_ctor_set(v___x_3508_, 3, v___x_3507_);
lean_ctor_set(v___x_3508_, 4, v___x_3506_);
lean_ctor_set(v___x_3508_, 5, v___x_3506_);
lean_ctor_set(v___x_3508_, 6, v___x_3506_);
lean_ctor_set(v___x_3508_, 7, v___x_3506_);
lean_ctor_set(v___x_3508_, 8, v___x_3506_);
lean_ctor_set(v___x_3508_, 9, v___x_3506_);
lean_ctor_set(v___x_3508_, 10, v___x_3506_);
return v___x_3508_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3509_ = lean_unsigned_to_nat(32u);
v___x_3510_ = lean_mk_empty_array_with_capacity(v___x_3509_);
v___x_3511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3510_);
return v___x_3511_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3512_ = ((size_t)5ULL);
v___x_3513_ = lean_unsigned_to_nat(0u);
v___x_3514_ = lean_unsigned_to_nat(32u);
v___x_3515_ = lean_mk_empty_array_with_capacity(v___x_3514_);
v___x_3516_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__3);
v___x_3517_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3517_, 0, v___x_3516_);
lean_ctor_set(v___x_3517_, 1, v___x_3515_);
lean_ctor_set(v___x_3517_, 2, v___x_3513_);
lean_ctor_set(v___x_3517_, 3, v___x_3513_);
lean_ctor_set_usize(v___x_3517_, 4, v___x_3512_);
return v___x_3517_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3518_ = lean_box(1);
v___x_3519_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__4);
v___x_3520_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1);
v___x_3521_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3520_);
lean_ctor_set(v___x_3521_, 1, v___x_3519_);
lean_ctor_set(v___x_3521_, 2, v___x_3518_);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(lean_object* v_msgData_3522_, lean_object* v___y_3523_){
_start:
{
lean_object* v___x_3525_; lean_object* v_env_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v_scopes_3529_; lean_object* v___x_3530_; lean_object* v_opts_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3525_ = lean_st_ref_get(v___y_3523_);
v_env_3526_ = lean_ctor_get(v___x_3525_, 0);
lean_inc_ref(v_env_3526_);
lean_dec(v___x_3525_);
v___x_3527_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3528_ = lean_st_ref_get(v___y_3523_);
v_scopes_3529_ = lean_ctor_get(v___x_3528_, 2);
lean_inc(v_scopes_3529_);
lean_dec(v___x_3528_);
v___x_3530_ = l_List_head_x21___redArg(v___x_3527_, v_scopes_3529_);
lean_dec(v_scopes_3529_);
v_opts_3531_ = lean_ctor_get(v___x_3530_, 1);
lean_inc_ref(v_opts_3531_);
lean_dec(v___x_3530_);
v___x_3532_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2);
v___x_3533_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5);
v___x_3534_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3534_, 0, v_env_3526_);
lean_ctor_set(v___x_3534_, 1, v___x_3532_);
lean_ctor_set(v___x_3534_, 2, v___x_3533_);
lean_ctor_set(v___x_3534_, 3, v_opts_3531_);
v___x_3535_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3534_);
lean_ctor_set(v___x_3535_, 1, v_msgData_3522_);
v___x_3536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3535_);
return v___x_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___boxed(lean_object* v_msgData_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_){
_start:
{
lean_object* v_res_3540_; 
v_res_3540_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_msgData_3537_, v___y_3538_);
lean_dec(v___y_3538_);
return v_res_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11___redArg(lean_object* v_msgData_3541_, lean_object* v_macroStack_3542_, lean_object* v___y_3543_){
_start:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v_scopes_3547_; lean_object* v___x_3548_; lean_object* v_opts_3549_; lean_object* v___x_3550_; uint8_t v___x_3551_; 
v___x_3545_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3546_ = lean_st_ref_get(v___y_3543_);
v_scopes_3547_ = lean_ctor_get(v___x_3546_, 2);
lean_inc(v_scopes_3547_);
lean_dec(v___x_3546_);
v___x_3548_ = l_List_head_x21___redArg(v___x_3545_, v_scopes_3547_);
lean_dec(v_scopes_3547_);
v_opts_3549_ = lean_ctor_get(v___x_3548_, 1);
lean_inc_ref(v_opts_3549_);
lean_dec(v___x_3548_);
v___x_3550_ = l_Lean_Elab_pp_macroStack;
v___x_3551_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(v_opts_3549_, v___x_3550_);
lean_dec_ref(v_opts_3549_);
if (v___x_3551_ == 0)
{
lean_object* v___x_3552_; 
lean_dec(v_macroStack_3542_);
v___x_3552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3552_, 0, v_msgData_3541_);
return v___x_3552_;
}
else
{
if (lean_obj_tag(v_macroStack_3542_) == 0)
{
lean_object* v___x_3553_; 
v___x_3553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3553_, 0, v_msgData_3541_);
return v___x_3553_;
}
else
{
lean_object* v_head_3554_; lean_object* v_after_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3570_; 
v_head_3554_ = lean_ctor_get(v_macroStack_3542_, 0);
lean_inc(v_head_3554_);
v_after_3555_ = lean_ctor_get(v_head_3554_, 1);
v_isSharedCheck_3570_ = !lean_is_exclusive(v_head_3554_);
if (v_isSharedCheck_3570_ == 0)
{
lean_object* v_unused_3571_; 
v_unused_3571_ = lean_ctor_get(v_head_3554_, 0);
lean_dec(v_unused_3571_);
v___x_3557_ = v_head_3554_;
v_isShared_3558_ = v_isSharedCheck_3570_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_after_3555_);
lean_dec(v_head_3554_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3570_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3559_; lean_object* v___x_3561_; 
v___x_3559_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0);
if (v_isShared_3558_ == 0)
{
lean_ctor_set_tag(v___x_3557_, 7);
lean_ctor_set(v___x_3557_, 1, v___x_3559_);
lean_ctor_set(v___x_3557_, 0, v_msgData_3541_);
v___x_3561_ = v___x_3557_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_msgData_3541_);
lean_ctor_set(v_reuseFailAlloc_3569_, 1, v___x_3559_);
v___x_3561_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v_msgData_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3562_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_3563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3563_, 0, v___x_3561_);
lean_ctor_set(v___x_3563_, 1, v___x_3562_);
v___x_3564_ = l_Lean_MessageData_ofSyntax(v_after_3555_);
v___x_3565_ = l_Lean_indentD(v___x_3564_);
v_msgData_3566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_3566_, 0, v___x_3563_);
lean_ctor_set(v_msgData_3566_, 1, v___x_3565_);
v___x_3567_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12(v_msgData_3566_, v_macroStack_3542_);
v___x_3568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3568_, 0, v___x_3567_);
return v___x_3568_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_msgData_3572_, lean_object* v_macroStack_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11___redArg(v_msgData_3572_, v_macroStack_3573_, v___y_3574_);
lean_dec(v___y_3574_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9___redArg(lean_object* v_msg_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
lean_object* v___x_3581_; 
v___x_3581_ = l_Lean_Elab_Command_getRef___redArg(v___y_3578_);
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_object* v_a_3582_; lean_object* v_macroStack_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v_a_3586_; lean_object* v___x_3587_; lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3596_; 
v_a_3582_ = lean_ctor_get(v___x_3581_, 0);
lean_inc(v_a_3582_);
lean_dec_ref_known(v___x_3581_, 1);
v_macroStack_3583_ = lean_ctor_get(v___y_3578_, 4);
v___x_3584_ = l_Lean_Elab_getBetterRef(v_a_3582_, v_macroStack_3583_);
lean_dec(v_a_3582_);
v___x_3585_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_msg_3577_, v___y_3579_);
v_a_3586_ = lean_ctor_get(v___x_3585_, 0);
lean_inc(v_a_3586_);
lean_dec_ref(v___x_3585_);
lean_inc(v_macroStack_3583_);
v___x_3587_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11___redArg(v_a_3586_, v_macroStack_3583_, v___y_3579_);
v_a_3588_ = lean_ctor_get(v___x_3587_, 0);
v_isSharedCheck_3596_ = !lean_is_exclusive(v___x_3587_);
if (v_isSharedCheck_3596_ == 0)
{
v___x_3590_ = v___x_3587_;
v_isShared_3591_ = v_isSharedCheck_3596_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3587_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3596_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3592_; lean_object* v___x_3594_; 
v___x_3592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3584_);
lean_ctor_set(v___x_3592_, 1, v_a_3588_);
if (v_isShared_3591_ == 0)
{
lean_ctor_set_tag(v___x_3590_, 1);
lean_ctor_set(v___x_3590_, 0, v___x_3592_);
v___x_3594_ = v___x_3590_;
goto v_reusejp_3593_;
}
else
{
lean_object* v_reuseFailAlloc_3595_; 
v_reuseFailAlloc_3595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3595_, 0, v___x_3592_);
v___x_3594_ = v_reuseFailAlloc_3595_;
goto v_reusejp_3593_;
}
v_reusejp_3593_:
{
return v___x_3594_;
}
}
}
else
{
lean_object* v_a_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3604_; 
lean_dec_ref(v_msg_3577_);
v_a_3597_ = lean_ctor_get(v___x_3581_, 0);
v_isSharedCheck_3604_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3599_ = v___x_3581_;
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_a_3597_);
lean_dec(v___x_3581_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___x_3602_; 
if (v_isShared_3600_ == 0)
{
v___x_3602_ = v___x_3599_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_a_3597_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
return v___x_3602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_msg_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_){
_start:
{
lean_object* v_res_3609_; 
v_res_3609_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_3605_, v___y_3606_, v___y_3607_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
return v_res_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(lean_object* v_ref_3610_, lean_object* v_msg_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_){
_start:
{
lean_object* v___x_3615_; 
v___x_3615_ = l_Lean_Elab_Command_getRef___redArg(v___y_3612_);
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v_a_3616_; lean_object* v_fileName_3617_; lean_object* v_fileMap_3618_; lean_object* v_currRecDepth_3619_; lean_object* v_cmdPos_3620_; lean_object* v_macroStack_3621_; lean_object* v_quotContext_x3f_3622_; lean_object* v_currMacroScope_3623_; lean_object* v_snap_x3f_3624_; lean_object* v_cancelTk_x3f_3625_; uint8_t v_suppressElabErrors_3626_; lean_object* v_ref_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; 
v_a_3616_ = lean_ctor_get(v___x_3615_, 0);
lean_inc(v_a_3616_);
lean_dec_ref_known(v___x_3615_, 1);
v_fileName_3617_ = lean_ctor_get(v___y_3612_, 0);
v_fileMap_3618_ = lean_ctor_get(v___y_3612_, 1);
v_currRecDepth_3619_ = lean_ctor_get(v___y_3612_, 2);
v_cmdPos_3620_ = lean_ctor_get(v___y_3612_, 3);
v_macroStack_3621_ = lean_ctor_get(v___y_3612_, 4);
v_quotContext_x3f_3622_ = lean_ctor_get(v___y_3612_, 5);
v_currMacroScope_3623_ = lean_ctor_get(v___y_3612_, 6);
v_snap_x3f_3624_ = lean_ctor_get(v___y_3612_, 8);
v_cancelTk_x3f_3625_ = lean_ctor_get(v___y_3612_, 9);
v_suppressElabErrors_3626_ = lean_ctor_get_uint8(v___y_3612_, sizeof(void*)*10);
v_ref_3627_ = l_Lean_replaceRef(v_ref_3610_, v_a_3616_);
lean_dec(v_a_3616_);
lean_inc(v_cancelTk_x3f_3625_);
lean_inc(v_snap_x3f_3624_);
lean_inc(v_currMacroScope_3623_);
lean_inc(v_quotContext_x3f_3622_);
lean_inc(v_macroStack_3621_);
lean_inc(v_cmdPos_3620_);
lean_inc(v_currRecDepth_3619_);
lean_inc_ref(v_fileMap_3618_);
lean_inc_ref(v_fileName_3617_);
v___x_3628_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_3628_, 0, v_fileName_3617_);
lean_ctor_set(v___x_3628_, 1, v_fileMap_3618_);
lean_ctor_set(v___x_3628_, 2, v_currRecDepth_3619_);
lean_ctor_set(v___x_3628_, 3, v_cmdPos_3620_);
lean_ctor_set(v___x_3628_, 4, v_macroStack_3621_);
lean_ctor_set(v___x_3628_, 5, v_quotContext_x3f_3622_);
lean_ctor_set(v___x_3628_, 6, v_currMacroScope_3623_);
lean_ctor_set(v___x_3628_, 7, v_ref_3627_);
lean_ctor_set(v___x_3628_, 8, v_snap_x3f_3624_);
lean_ctor_set(v___x_3628_, 9, v_cancelTk_x3f_3625_);
lean_ctor_set_uint8(v___x_3628_, sizeof(void*)*10, v_suppressElabErrors_3626_);
v___x_3629_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_3611_, v___x_3628_, v___y_3613_);
lean_dec_ref_known(v___x_3628_, 10);
return v___x_3629_;
}
else
{
lean_object* v_a_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3637_; 
lean_dec_ref(v_msg_3611_);
v_a_3630_ = lean_ctor_get(v___x_3615_, 0);
v_isSharedCheck_3637_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3632_ = v___x_3615_;
v_isShared_3633_ = v_isSharedCheck_3637_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_a_3630_);
lean_dec(v___x_3615_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3637_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v___x_3635_; 
if (v_isShared_3633_ == 0)
{
v___x_3635_ = v___x_3632_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_a_3630_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_ref_3638_, lean_object* v_msg_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_){
_start:
{
lean_object* v_res_3643_; 
v_res_3643_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v_ref_3638_, v_msg_3639_, v___y_3640_, v___y_3641_);
lean_dec(v___y_3641_);
lean_dec_ref(v___y_3640_);
lean_dec(v_ref_3638_);
return v_res_3643_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3645_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__0));
v___x_3646_ = l_Lean_stringToMessageData(v___x_3645_);
return v___x_3646_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3648_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__2));
v___x_3649_ = l_Lean_stringToMessageData(v___x_3648_);
return v___x_3649_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; 
v___x_3651_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__4));
v___x_3652_ = l_Lean_stringToMessageData(v___x_3651_);
return v___x_3652_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3654_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__6));
v___x_3655_ = l_Lean_stringToMessageData(v___x_3654_);
return v___x_3655_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3657_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__8));
v___x_3658_ = l_Lean_stringToMessageData(v___x_3657_);
return v___x_3658_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__11(void){
_start:
{
lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3660_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__10));
v___x_3661_ = l_Lean_stringToMessageData(v___x_3660_);
return v___x_3661_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__13(void){
_start:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3663_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__12));
v___x_3664_ = l_Lean_stringToMessageData(v___x_3663_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_msg_3665_, lean_object* v_declHint_3666_, lean_object* v___y_3667_){
_start:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v_env_3671_; uint8_t v___x_3672_; 
v___x_3669_ = lean_box(0);
v___x_3670_ = lean_st_ref_get(v___y_3667_);
v_env_3671_ = lean_ctor_get(v___x_3670_, 0);
lean_inc_ref(v_env_3671_);
lean_dec(v___x_3670_);
v___x_3672_ = l_Lean_Name_isAnonymous(v_declHint_3666_);
if (v___x_3672_ == 0)
{
uint8_t v_isExporting_3673_; 
v_isExporting_3673_ = lean_ctor_get_uint8(v_env_3671_, sizeof(void*)*8);
if (v_isExporting_3673_ == 0)
{
lean_object* v___x_3674_; 
lean_dec_ref(v_env_3671_);
lean_dec(v_declHint_3666_);
v___x_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3674_, 0, v_msg_3665_);
return v___x_3674_;
}
else
{
lean_object* v___x_3675_; uint8_t v___x_3676_; 
lean_inc_ref(v_env_3671_);
v___x_3675_ = l_Lean_Environment_setExporting(v_env_3671_, v___x_3672_);
lean_inc(v_declHint_3666_);
lean_inc_ref(v___x_3675_);
v___x_3676_ = l_Lean_Environment_contains(v___x_3675_, v_declHint_3666_, v_isExporting_3673_);
if (v___x_3676_ == 0)
{
lean_object* v___x_3677_; 
lean_dec_ref(v___x_3675_);
lean_dec_ref(v_env_3671_);
lean_dec(v_declHint_3666_);
v___x_3677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3677_, 0, v_msg_3665_);
return v___x_3677_;
}
else
{
lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v_c_3683_; lean_object* v___x_3684_; 
v___x_3678_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2);
v___x_3679_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5);
v___x_3680_ = l_Lean_Options_empty;
v___x_3681_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3675_);
lean_ctor_set(v___x_3681_, 1, v___x_3678_);
lean_ctor_set(v___x_3681_, 2, v___x_3679_);
lean_ctor_set(v___x_3681_, 3, v___x_3680_);
lean_inc(v_declHint_3666_);
v___x_3682_ = l_Lean_MessageData_ofConstName(v_declHint_3666_, v___x_3672_);
v_c_3683_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3683_, 0, v___x_3681_);
lean_ctor_set(v_c_3683_, 1, v___x_3682_);
v___x_3684_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3671_, v_declHint_3666_);
if (lean_obj_tag(v___x_3684_) == 0)
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
lean_dec_ref(v_env_3671_);
lean_dec(v_declHint_3666_);
v___x_3685_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_3686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3686_, 0, v___x_3685_);
lean_ctor_set(v___x_3686_, 1, v_c_3683_);
v___x_3687_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_3688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3686_);
lean_ctor_set(v___x_3688_, 1, v___x_3687_);
v___x_3689_ = l_Lean_MessageData_note(v___x_3688_);
v___x_3690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3690_, 0, v_msg_3665_);
lean_ctor_set(v___x_3690_, 1, v___x_3689_);
v___x_3691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3690_);
return v___x_3691_;
}
else
{
lean_object* v_val_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3726_; 
v_val_3692_ = lean_ctor_get(v___x_3684_, 0);
v_isSharedCheck_3726_ = !lean_is_exclusive(v___x_3684_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3694_ = v___x_3684_;
v_isShared_3695_ = v_isSharedCheck_3726_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_val_3692_);
lean_dec(v___x_3684_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3726_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v_mod_3698_; uint8_t v___x_3699_; 
v___x_3696_ = l_Lean_Environment_header(v_env_3671_);
lean_dec_ref(v_env_3671_);
v___x_3697_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3696_);
v_mod_3698_ = lean_array_get(v___x_3669_, v___x_3697_, v_val_3692_);
lean_dec(v_val_3692_);
lean_dec_ref(v___x_3697_);
v___x_3699_ = l_Lean_isPrivateName(v_declHint_3666_);
lean_dec(v_declHint_3666_);
if (v___x_3699_ == 0)
{
lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3711_; 
v___x_3700_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__5);
v___x_3701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3700_);
lean_ctor_set(v___x_3701_, 1, v_c_3683_);
v___x_3702_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_3703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3701_);
lean_ctor_set(v___x_3703_, 1, v___x_3702_);
v___x_3704_ = l_Lean_MessageData_ofName(v_mod_3698_);
v___x_3705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3703_);
lean_ctor_set(v___x_3705_, 1, v___x_3704_);
v___x_3706_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__9);
v___x_3707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3705_);
lean_ctor_set(v___x_3707_, 1, v___x_3706_);
v___x_3708_ = l_Lean_MessageData_note(v___x_3707_);
v___x_3709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3709_, 0, v_msg_3665_);
lean_ctor_set(v___x_3709_, 1, v___x_3708_);
if (v_isShared_3695_ == 0)
{
lean_ctor_set_tag(v___x_3694_, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3709_);
v___x_3711_ = v___x_3694_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v___x_3709_);
v___x_3711_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
return v___x_3711_;
}
}
else
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3724_; 
v___x_3713_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_3714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3713_);
lean_ctor_set(v___x_3714_, 1, v_c_3683_);
v___x_3715_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__11);
v___x_3716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3714_);
lean_ctor_set(v___x_3716_, 1, v___x_3715_);
v___x_3717_ = l_Lean_MessageData_ofName(v_mod_3698_);
v___x_3718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3716_);
lean_ctor_set(v___x_3718_, 1, v___x_3717_);
v___x_3719_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__13);
v___x_3720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3718_);
lean_ctor_set(v___x_3720_, 1, v___x_3719_);
v___x_3721_ = l_Lean_MessageData_note(v___x_3720_);
v___x_3722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3722_, 0, v_msg_3665_);
lean_ctor_set(v___x_3722_, 1, v___x_3721_);
if (v_isShared_3695_ == 0)
{
lean_ctor_set_tag(v___x_3694_, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3722_);
v___x_3724_ = v___x_3694_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3722_);
v___x_3724_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
return v___x_3724_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3727_; 
lean_dec_ref(v_env_3671_);
lean_dec(v_declHint_3666_);
v___x_3727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3727_, 0, v_msg_3665_);
return v___x_3727_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_msg_3728_, lean_object* v_declHint_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_){
_start:
{
lean_object* v_res_3732_; 
v_res_3732_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_3728_, v_declHint_3729_, v___y_3730_);
lean_dec(v___y_3730_);
return v_res_3732_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6(lean_object* v_msg_3733_, lean_object* v_declHint_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_){
_start:
{
lean_object* v___x_3738_; lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3748_; 
v___x_3738_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_3733_, v_declHint_3734_, v___y_3736_);
v_a_3739_ = lean_ctor_get(v___x_3738_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3738_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3741_ = v___x_3738_;
v_isShared_3742_ = v_isSharedCheck_3748_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3738_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3748_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3746_; 
v___x_3743_ = l_Lean_unknownIdentifierMessageTag;
v___x_3744_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3744_, 0, v___x_3743_);
lean_ctor_set(v___x_3744_, 1, v_a_3739_);
if (v_isShared_3742_ == 0)
{
lean_ctor_set(v___x_3741_, 0, v___x_3744_);
v___x_3746_ = v___x_3741_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3744_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___boxed(lean_object* v_msg_3749_, lean_object* v_declHint_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
lean_object* v_res_3754_; 
v_res_3754_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_3749_, v_declHint_3750_, v___y_3751_, v___y_3752_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
return v_res_3754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_3755_, lean_object* v_msg_3756_, lean_object* v_declHint_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
lean_object* v___x_3761_; lean_object* v_a_3762_; lean_object* v___x_3763_; 
v___x_3761_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_3756_, v_declHint_3757_, v___y_3758_, v___y_3759_);
v_a_3762_ = lean_ctor_get(v___x_3761_, 0);
lean_inc(v_a_3762_);
lean_dec_ref(v___x_3761_);
v___x_3763_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v_ref_3755_, v_a_3762_, v___y_3758_, v___y_3759_);
return v___x_3763_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_3764_, lean_object* v_msg_3765_, lean_object* v_declHint_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_){
_start:
{
lean_object* v_res_3770_; 
v_res_3770_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3764_, v_msg_3765_, v_declHint_3766_, v___y_3767_, v___y_3768_);
lean_dec(v___y_3768_);
lean_dec_ref(v___y_3767_);
lean_dec(v_ref_3764_);
return v_res_3770_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3772_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___closed__0));
v___x_3773_ = l_Lean_stringToMessageData(v___x_3772_);
return v___x_3773_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_3774_, lean_object* v_constName_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_){
_start:
{
lean_object* v___x_3779_; uint8_t v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; 
v___x_3779_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_3780_ = 0;
lean_inc(v_constName_3775_);
v___x_3781_ = l_Lean_MessageData_ofConstName(v_constName_3775_, v___x_3780_);
v___x_3782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3782_, 0, v___x_3779_);
lean_ctor_set(v___x_3782_, 1, v___x_3781_);
v___x_3783_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1);
v___x_3784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3782_);
lean_ctor_set(v___x_3784_, 1, v___x_3783_);
v___x_3785_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3774_, v___x_3784_, v_constName_3775_, v___y_3776_, v___y_3777_);
return v___x_3785_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_3786_, lean_object* v_constName_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_){
_start:
{
lean_object* v_res_3791_; 
v_res_3791_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3786_, v_constName_3787_, v___y_3788_, v___y_3789_);
lean_dec(v___y_3789_);
lean_dec_ref(v___y_3788_);
lean_dec(v_ref_3786_);
return v_res_3791_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_){
_start:
{
lean_object* v___x_3796_; 
v___x_3796_ = l_Lean_Elab_Command_getRef___redArg(v___y_3793_);
if (lean_obj_tag(v___x_3796_) == 0)
{
lean_object* v_a_3797_; lean_object* v___x_3798_; 
v_a_3797_ = lean_ctor_get(v___x_3796_, 0);
lean_inc(v_a_3797_);
lean_dec_ref_known(v___x_3796_, 1);
v___x_3798_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_a_3797_, v_constName_3792_, v___y_3793_, v___y_3794_);
lean_dec(v_a_3797_);
return v___x_3798_;
}
else
{
lean_object* v_a_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3806_; 
lean_dec(v_constName_3792_);
v_a_3799_ = lean_ctor_get(v___x_3796_, 0);
v_isSharedCheck_3806_ = !lean_is_exclusive(v___x_3796_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3801_ = v___x_3796_;
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_a_3799_);
lean_dec(v___x_3796_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3804_; 
if (v_isShared_3802_ == 0)
{
v___x_3804_ = v___x_3801_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_a_3799_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
lean_object* v_res_3811_; 
v_res_3811_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1___redArg(v_constName_3807_, v___y_3808_, v___y_3809_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
return v_res_3811_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0(lean_object* v_constName_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_){
_start:
{
lean_object* v___x_3816_; lean_object* v_env_3817_; uint8_t v___x_3818_; lean_object* v___x_3819_; 
v___x_3816_ = lean_st_ref_get(v___y_3814_);
v_env_3817_ = lean_ctor_get(v___x_3816_, 0);
lean_inc_ref(v_env_3817_);
lean_dec(v___x_3816_);
v___x_3818_ = 0;
lean_inc(v_constName_3812_);
v___x_3819_ = l_Lean_Environment_find_x3f(v_env_3817_, v_constName_3812_, v___x_3818_);
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_object* v___x_3820_; 
v___x_3820_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1___redArg(v_constName_3812_, v___y_3813_, v___y_3814_);
return v___x_3820_;
}
else
{
lean_object* v_val_3821_; lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3828_; 
lean_dec(v_constName_3812_);
v_val_3821_ = lean_ctor_get(v___x_3819_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v___x_3819_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3823_ = v___x_3819_;
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
else
{
lean_inc(v_val_3821_);
lean_dec(v___x_3819_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v___x_3826_; 
if (v_isShared_3824_ == 0)
{
lean_ctor_set_tag(v___x_3823_, 0);
v___x_3826_ = v___x_3823_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v_val_3821_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
return v___x_3826_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0___boxed(lean_object* v_constName_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_){
_start:
{
lean_object* v_res_3833_; 
v_res_3833_ = l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0(v_constName_3829_, v___y_3830_, v___y_3831_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
return v_res_3833_;
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__1(uint8_t v___x_3834_, lean_object* v_x_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
if (lean_obj_tag(v_x_3835_) == 0)
{
uint8_t v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; 
v___x_3839_ = 1;
v___x_3840_ = lean_box(v___x_3839_);
v___x_3841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3841_, 0, v___x_3840_);
return v___x_3841_;
}
else
{
lean_object* v_head_3842_; lean_object* v_tail_3843_; lean_object* v___y_3845_; uint8_t v_a_3846_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
v_head_3842_ = lean_ctor_get(v_x_3835_, 0);
lean_inc(v_head_3842_);
v_tail_3843_ = lean_ctor_get(v_x_3835_, 1);
lean_inc(v_tail_3843_);
lean_dec_ref_known(v_x_3835_, 2);
v___x_3848_ = lean_unsigned_to_nat(0u);
v___x_3849_ = l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0(v_head_3842_, v___y_3836_, v___y_3837_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3865_; 
v_a_3850_ = lean_ctor_get(v___x_3849_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3852_ = v___x_3849_;
v_isShared_3853_ = v_isSharedCheck_3865_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_dec(v___x_3849_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3865_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
if (lean_obj_tag(v_a_3850_) == 6)
{
lean_object* v_val_3854_; lean_object* v_numFields_3855_; uint8_t v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3859_; 
v_val_3854_ = lean_ctor_get(v_a_3850_, 0);
lean_inc_ref(v_val_3854_);
lean_dec_ref_known(v_a_3850_, 1);
v_numFields_3855_ = lean_ctor_get(v_val_3854_, 4);
lean_inc(v_numFields_3855_);
lean_dec_ref(v_val_3854_);
v___x_3856_ = lean_nat_dec_eq(v_numFields_3855_, v___x_3848_);
lean_dec(v_numFields_3855_);
v___x_3857_ = lean_box(v___x_3856_);
if (v_isShared_3853_ == 0)
{
lean_ctor_set(v___x_3852_, 0, v___x_3857_);
v___x_3859_ = v___x_3852_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v___x_3857_);
v___x_3859_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
v___y_3845_ = v___x_3859_;
v_a_3846_ = v___x_3856_;
goto v___jp_3844_;
}
}
else
{
lean_object* v___x_3861_; lean_object* v___x_3863_; 
lean_dec(v_a_3850_);
v___x_3861_ = lean_box(v___x_3834_);
if (v_isShared_3853_ == 0)
{
lean_ctor_set(v___x_3852_, 0, v___x_3861_);
v___x_3863_ = v___x_3852_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v___x_3861_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
v___y_3845_ = v___x_3863_;
v_a_3846_ = v___x_3834_;
goto v___jp_3844_;
}
}
}
}
else
{
lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3873_; 
lean_dec(v_tail_3843_);
v_a_3866_ = lean_ctor_get(v___x_3849_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3868_ = v___x_3849_;
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v___x_3849_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3871_; 
if (v_isShared_3869_ == 0)
{
v___x_3871_ = v___x_3868_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_a_3866_);
v___x_3871_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
return v___x_3871_;
}
}
}
v___jp_3844_:
{
if (v_a_3846_ == 0)
{
lean_dec(v_tail_3843_);
return v___y_3845_;
}
else
{
lean_dec_ref(v___y_3845_);
v_x_3835_ = v_tail_3843_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__1___boxed(lean_object* v___x_3874_, lean_object* v_x_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_){
_start:
{
uint8_t v___x_4446__boxed_3879_; lean_object* v_res_3880_; 
v___x_4446__boxed_3879_ = lean_unbox(v___x_3874_);
v_res_3880_ = l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__1(v___x_4446__boxed_3879_, v_x_3875_, v___y_3876_, v___y_3877_);
lean_dec(v___y_3877_);
lean_dec_ref(v___y_3876_);
return v_res_3880_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0(lean_object* v_declName_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_){
_start:
{
lean_object* v___x_3885_; 
v___x_3885_ = l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0(v_declName_3881_, v___y_3882_, v___y_3883_);
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_object* v_a_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3941_; 
v_a_3886_ = lean_ctor_get(v___x_3885_, 0);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___x_3885_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3888_ = v___x_3885_;
v_isShared_3889_ = v_isSharedCheck_3941_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_a_3886_);
lean_dec(v___x_3885_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3941_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
if (lean_obj_tag(v_a_3886_) == 5)
{
lean_object* v_val_3890_; lean_object* v_toConstantVal_3891_; lean_object* v_numParams_3892_; lean_object* v_numIndices_3893_; lean_object* v_ctors_3894_; uint8_t v_isRec_3895_; uint8_t v_isUnsafe_3896_; lean_object* v_type_3897_; uint8_t v___x_3898_; 
v_val_3890_ = lean_ctor_get(v_a_3886_, 0);
lean_inc_ref(v_val_3890_);
lean_dec_ref_known(v_a_3886_, 1);
v_toConstantVal_3891_ = lean_ctor_get(v_val_3890_, 0);
v_numParams_3892_ = lean_ctor_get(v_val_3890_, 1);
lean_inc(v_numParams_3892_);
v_numIndices_3893_ = lean_ctor_get(v_val_3890_, 2);
lean_inc(v_numIndices_3893_);
v_ctors_3894_ = lean_ctor_get(v_val_3890_, 4);
lean_inc(v_ctors_3894_);
v_isRec_3895_ = lean_ctor_get_uint8(v_val_3890_, sizeof(void*)*6);
v_isUnsafe_3896_ = lean_ctor_get_uint8(v_val_3890_, sizeof(void*)*6 + 1);
v_type_3897_ = lean_ctor_get(v_toConstantVal_3891_, 2);
v___x_3898_ = l_Lean_Expr_isProp(v_type_3897_);
if (v___x_3898_ == 0)
{
lean_object* v___x_3899_; lean_object* v___x_3900_; uint8_t v___x_3901_; 
v___x_3899_ = l_Lean_InductiveVal_numTypeFormers(v_val_3890_);
lean_dec_ref(v_val_3890_);
v___x_3900_ = lean_unsigned_to_nat(1u);
v___x_3901_ = lean_nat_dec_eq(v___x_3899_, v___x_3900_);
lean_dec(v___x_3899_);
if (v___x_3901_ == 0)
{
lean_object* v___x_3902_; lean_object* v___x_3904_; 
lean_dec(v_ctors_3894_);
lean_dec(v_numIndices_3893_);
lean_dec(v_numParams_3892_);
v___x_3902_ = lean_box(v___x_3901_);
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 0, v___x_3902_);
v___x_3904_ = v___x_3888_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v___x_3902_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
else
{
lean_object* v___x_3906_; uint8_t v___x_3907_; 
v___x_3906_ = lean_unsigned_to_nat(0u);
v___x_3907_ = lean_nat_dec_eq(v_numIndices_3893_, v___x_3906_);
lean_dec(v_numIndices_3893_);
if (v___x_3907_ == 0)
{
lean_object* v___x_3908_; lean_object* v___x_3910_; 
lean_dec(v_ctors_3894_);
lean_dec(v_numParams_3892_);
v___x_3908_ = lean_box(v___x_3907_);
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 0, v___x_3908_);
v___x_3910_ = v___x_3888_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v___x_3908_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
else
{
uint8_t v___x_3912_; 
v___x_3912_ = lean_nat_dec_eq(v_numParams_3892_, v___x_3906_);
lean_dec(v_numParams_3892_);
if (v___x_3912_ == 0)
{
lean_object* v___x_3913_; lean_object* v___x_3915_; 
lean_dec(v_ctors_3894_);
v___x_3913_ = lean_box(v___x_3912_);
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 0, v___x_3913_);
v___x_3915_ = v___x_3888_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v___x_3913_);
v___x_3915_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
return v___x_3915_;
}
}
else
{
uint8_t v___x_3917_; 
v___x_3917_ = l_List_isEmpty___redArg(v_ctors_3894_);
if (v___x_3917_ == 0)
{
if (v_isRec_3895_ == 0)
{
if (v_isUnsafe_3896_ == 0)
{
lean_object* v___x_3918_; 
lean_del_object(v___x_3888_);
v___x_3918_ = l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__1(v_isUnsafe_3896_, v_ctors_3894_, v___y_3882_, v___y_3883_);
return v___x_3918_;
}
else
{
lean_object* v___x_3919_; lean_object* v___x_3921_; 
lean_dec(v_ctors_3894_);
v___x_3919_ = lean_box(v_isRec_3895_);
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 0, v___x_3919_);
v___x_3921_ = v___x_3888_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v___x_3919_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
}
else
{
lean_object* v___x_3923_; lean_object* v___x_3925_; 
lean_dec(v_ctors_3894_);
v___x_3923_ = lean_box(v___x_3917_);
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 0, v___x_3923_);
v___x_3925_ = v___x_3888_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v___x_3923_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
else
{
lean_object* v___x_3927_; lean_object* v___x_3929_; 
lean_dec(v_ctors_3894_);
v___x_3927_ = lean_box(v___x_3898_);
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 0, v___x_3927_);
v___x_3929_ = v___x_3888_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v___x_3927_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
}
}
}
else
{
uint8_t v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3934_; 
lean_dec(v_ctors_3894_);
lean_dec(v_numIndices_3893_);
lean_dec(v_numParams_3892_);
lean_dec_ref(v_val_3890_);
v___x_3931_ = 0;
v___x_3932_ = lean_box(v___x_3931_);
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 0, v___x_3932_);
v___x_3934_ = v___x_3888_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v___x_3932_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
return v___x_3934_;
}
}
}
else
{
uint8_t v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3939_; 
lean_dec(v_a_3886_);
v___x_3936_ = 0;
v___x_3937_ = lean_box(v___x_3936_);
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 0, v___x_3937_);
v___x_3939_ = v___x_3888_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v___x_3937_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
}
}
else
{
lean_object* v_a_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3949_; 
v_a_3942_ = lean_ctor_get(v___x_3885_, 0);
v_isSharedCheck_3949_ = !lean_is_exclusive(v___x_3885_);
if (v_isSharedCheck_3949_ == 0)
{
v___x_3944_ = v___x_3885_;
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_a_3942_);
lean_dec(v___x_3885_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3947_; 
if (v_isShared_3945_ == 0)
{
v___x_3947_ = v___x_3944_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v_a_3942_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0___boxed(lean_object* v_declName_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_){
_start:
{
lean_object* v_res_3954_; 
v_res_3954_ = l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0(v_declName_3950_, v___y_3951_, v___y_3952_);
lean_dec(v___y_3952_);
lean_dec_ref(v___y_3951_);
return v_res_3954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__1(lean_object* v_as_3955_, size_t v_i_3956_, size_t v_stop_3957_, lean_object* v_b_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_){
_start:
{
uint8_t v___x_3962_; 
v___x_3962_ = lean_usize_dec_eq(v_i_3956_, v_stop_3957_);
if (v___x_3962_ == 0)
{
lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3963_ = lean_array_uget_borrowed(v_as_3955_, v_i_3956_);
lean_inc(v___x_3963_);
v___x_3964_ = l_Lean_Elab_Command_elabCommand(v___x_3963_, v___y_3959_, v___y_3960_);
if (lean_obj_tag(v___x_3964_) == 0)
{
lean_object* v_a_3965_; size_t v___x_3966_; size_t v___x_3967_; 
v_a_3965_ = lean_ctor_get(v___x_3964_, 0);
lean_inc(v_a_3965_);
lean_dec_ref_known(v___x_3964_, 1);
v___x_3966_ = ((size_t)1ULL);
v___x_3967_ = lean_usize_add(v_i_3956_, v___x_3966_);
v_i_3956_ = v___x_3967_;
v_b_3958_ = v_a_3965_;
goto _start;
}
else
{
return v___x_3964_;
}
}
else
{
lean_object* v___x_3969_; 
v___x_3969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3969_, 0, v_b_3958_);
return v___x_3969_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__1___boxed(lean_object* v_as_3970_, lean_object* v_i_3971_, lean_object* v_stop_3972_, lean_object* v_b_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_){
_start:
{
size_t v_i_boxed_3977_; size_t v_stop_boxed_3978_; lean_object* v_res_3979_; 
v_i_boxed_3977_ = lean_unbox_usize(v_i_3971_);
lean_dec(v_i_3971_);
v_stop_boxed_3978_ = lean_unbox_usize(v_stop_3972_);
lean_dec(v_stop_3972_);
v_res_3979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__1(v_as_3970_, v_i_boxed_3977_, v_stop_boxed_3978_, v_b_3973_, v___y_3974_, v___y_3975_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
lean_dec_ref(v_as_3970_);
return v_res_3979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__1(lean_object* v_declName_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_){
_start:
{
lean_object* v___x_3984_; 
lean_inc(v_declName_3980_);
v___x_3984_ = l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0(v_declName_3980_, v___y_3981_, v___y_3982_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v_a_3985_; lean_object* v___y_3986_; lean_object* v___x_3987_; 
v_a_3985_ = lean_ctor_get(v___x_3984_, 0);
lean_inc(v_a_3985_);
lean_dec_ref_known(v___x_3984_, 1);
v___y_3986_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__0___boxed), 9, 2);
lean_closure_set(v___y_3986_, 0, v_a_3985_);
lean_closure_set(v___y_3986_, 1, v_declName_3980_);
v___x_3987_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___y_3986_, v___y_3981_, v___y_3982_);
if (lean_obj_tag(v___x_3987_) == 0)
{
lean_object* v_a_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_4009_; 
v_a_3988_ = lean_ctor_get(v___x_3987_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_3990_ = v___x_3987_;
v_isShared_3991_ = v_isSharedCheck_4009_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_a_3988_);
lean_dec(v___x_3987_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_4009_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; uint8_t v___x_3995_; 
v___x_3992_ = lean_unsigned_to_nat(0u);
v___x_3993_ = lean_array_get_size(v_a_3988_);
v___x_3994_ = lean_box(0);
v___x_3995_ = lean_nat_dec_lt(v___x_3992_, v___x_3993_);
if (v___x_3995_ == 0)
{
lean_object* v___x_3997_; 
lean_dec(v_a_3988_);
if (v_isShared_3991_ == 0)
{
lean_ctor_set(v___x_3990_, 0, v___x_3994_);
v___x_3997_ = v___x_3990_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v___x_3994_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
}
}
else
{
uint8_t v___x_3999_; 
v___x_3999_ = lean_nat_dec_le(v___x_3993_, v___x_3993_);
if (v___x_3999_ == 0)
{
if (v___x_3995_ == 0)
{
lean_object* v___x_4001_; 
lean_dec(v_a_3988_);
if (v_isShared_3991_ == 0)
{
lean_ctor_set(v___x_3990_, 0, v___x_3994_);
v___x_4001_ = v___x_3990_;
goto v_reusejp_4000_;
}
else
{
lean_object* v_reuseFailAlloc_4002_; 
v_reuseFailAlloc_4002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4002_, 0, v___x_3994_);
v___x_4001_ = v_reuseFailAlloc_4002_;
goto v_reusejp_4000_;
}
v_reusejp_4000_:
{
return v___x_4001_;
}
}
else
{
size_t v___x_4003_; size_t v___x_4004_; lean_object* v___x_4005_; 
lean_del_object(v___x_3990_);
v___x_4003_ = ((size_t)0ULL);
v___x_4004_ = lean_usize_of_nat(v___x_3993_);
v___x_4005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__1(v_a_3988_, v___x_4003_, v___x_4004_, v___x_3994_, v___y_3981_, v___y_3982_);
lean_dec(v_a_3988_);
return v___x_4005_;
}
}
else
{
size_t v___x_4006_; size_t v___x_4007_; lean_object* v___x_4008_; 
lean_del_object(v___x_3990_);
v___x_4006_ = ((size_t)0ULL);
v___x_4007_ = lean_usize_of_nat(v___x_3993_);
v___x_4008_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__1(v_a_3988_, v___x_4006_, v___x_4007_, v___x_3994_, v___y_3981_, v___y_3982_);
lean_dec(v_a_3988_);
return v___x_4008_;
}
}
}
}
else
{
lean_object* v_a_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4017_; 
v_a_4010_ = lean_ctor_get(v___x_3987_, 0);
v_isSharedCheck_4017_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_4017_ == 0)
{
v___x_4012_ = v___x_3987_;
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_a_4010_);
lean_dec(v___x_3987_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4017_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4015_; 
if (v_isShared_4013_ == 0)
{
v___x_4015_ = v___x_4012_;
goto v_reusejp_4014_;
}
else
{
lean_object* v_reuseFailAlloc_4016_; 
v_reuseFailAlloc_4016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_a_4010_);
v___x_4015_ = v_reuseFailAlloc_4016_;
goto v_reusejp_4014_;
}
v_reusejp_4014_:
{
return v___x_4015_;
}
}
}
}
else
{
lean_object* v_a_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4025_; 
lean_dec(v_declName_3980_);
v_a_4018_ = lean_ctor_get(v___x_3984_, 0);
v_isSharedCheck_4025_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_4025_ == 0)
{
v___x_4020_ = v___x_3984_;
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_a_4018_);
lean_dec(v___x_3984_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v___x_4023_; 
if (v_isShared_4021_ == 0)
{
v___x_4023_ = v___x_4020_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4024_; 
v_reuseFailAlloc_4024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4024_, 0, v_a_4018_);
v___x_4023_ = v_reuseFailAlloc_4024_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
return v___x_4023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__1___boxed(lean_object* v_declName_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_){
_start:
{
lean_object* v_res_4030_; 
v_res_4030_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__1(v_declName_4026_, v___y_4027_, v___y_4028_);
lean_dec(v___y_4028_);
lean_dec_ref(v___y_4027_);
return v_res_4030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance(lean_object* v_declName_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_){
_start:
{
lean_object* v___f_4035_; lean_object* v___x_4036_; 
lean_inc(v_declName_4031_);
v___f_4035_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__1___boxed), 4, 1);
lean_closure_set(v___f_4035_, 0, v_declName_4031_);
v___x_4036_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_declName_4031_, v___f_4035_, v_a_4032_, v_a_4033_);
return v___x_4036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___boxed(lean_object* v_declName_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_){
_start:
{
lean_object* v_res_4041_; 
v_res_4041_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance(v_declName_4037_, v_a_4038_, v_a_4039_);
lean_dec(v_a_4039_);
lean_dec_ref(v_a_4038_);
return v_res_4041_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4042_, lean_object* v_constName_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_){
_start:
{
lean_object* v___x_4047_; 
v___x_4047_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1___redArg(v_constName_4043_, v___y_4044_, v___y_4045_);
return v___x_4047_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_4048_, lean_object* v_constName_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_){
_start:
{
lean_object* v_res_4053_; 
v_res_4053_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1(v_00_u03b1_4048_, v_constName_4049_, v___y_4050_, v___y_4051_);
lean_dec(v___y_4051_);
lean_dec_ref(v___y_4050_);
return v_res_4053_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_4054_, lean_object* v_ref_4055_, lean_object* v_constName_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_){
_start:
{
lean_object* v___x_4060_; 
v___x_4060_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_4055_, v_constName_4056_, v___y_4057_, v___y_4058_);
return v___x_4060_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4061_, lean_object* v_ref_4062_, lean_object* v_constName_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_){
_start:
{
lean_object* v_res_4067_; 
v_res_4067_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_4061_, v_ref_4062_, v_constName_4063_, v___y_4064_, v___y_4065_);
lean_dec(v___y_4065_);
lean_dec_ref(v___y_4064_);
lean_dec(v_ref_4062_);
return v_res_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_4068_, lean_object* v_ref_4069_, lean_object* v_msg_4070_, lean_object* v_declHint_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_){
_start:
{
lean_object* v___x_4075_; 
v___x_4075_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_4069_, v_msg_4070_, v_declHint_4071_, v___y_4072_, v___y_4073_);
return v___x_4075_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_4076_, lean_object* v_ref_4077_, lean_object* v_msg_4078_, lean_object* v_declHint_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_){
_start:
{
lean_object* v_res_4083_; 
v_res_4083_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_4076_, v_ref_4077_, v_msg_4078_, v_declHint_4079_, v___y_4080_, v___y_4081_);
lean_dec(v___y_4081_);
lean_dec_ref(v___y_4080_);
lean_dec(v_ref_4077_);
return v_res_4083_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7(lean_object* v_msg_4084_, lean_object* v_declHint_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_){
_start:
{
lean_object* v___x_4089_; 
v___x_4089_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_4084_, v_declHint_4085_, v___y_4087_);
return v___x_4089_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___boxed(lean_object* v_msg_4090_, lean_object* v_declHint_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_){
_start:
{
lean_object* v_res_4095_; 
v_res_4095_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7(v_msg_4090_, v_declHint_4091_, v___y_4092_, v___y_4093_);
lean_dec(v___y_4093_);
lean_dec_ref(v___y_4092_);
return v_res_4095_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_4096_, lean_object* v_ref_4097_, lean_object* v_msg_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
lean_object* v___x_4102_; 
v___x_4102_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v_ref_4097_, v_msg_4098_, v___y_4099_, v___y_4100_);
return v___x_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_4103_, lean_object* v_ref_4104_, lean_object* v_msg_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_){
_start:
{
lean_object* v_res_4109_; 
v_res_4109_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7(v_00_u03b1_4103_, v_ref_4104_, v_msg_4105_, v___y_4106_, v___y_4107_);
lean_dec(v___y_4107_);
lean_dec_ref(v___y_4106_);
lean_dec(v_ref_4104_);
return v_res_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10(lean_object* v_msgData_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_){
_start:
{
lean_object* v___x_4114_; 
v___x_4114_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_msgData_4110_, v___y_4112_);
return v___x_4114_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___boxed(lean_object* v_msgData_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_){
_start:
{
lean_object* v_res_4119_; 
v_res_4119_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10(v_msgData_4115_, v___y_4116_, v___y_4117_);
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
return v_res_4119_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_4120_, lean_object* v_msg_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_){
_start:
{
lean_object* v___x_4125_; 
v___x_4125_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_4121_, v___y_4122_, v___y_4123_);
return v___x_4125_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4126_, lean_object* v_msg_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_){
_start:
{
lean_object* v_res_4131_; 
v_res_4131_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9(v_00_u03b1_4126_, v_msg_4127_, v___y_4128_, v___y_4129_);
lean_dec(v___y_4129_);
lean_dec_ref(v___y_4128_);
return v_res_4131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11(lean_object* v_msgData_4132_, lean_object* v_macroStack_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_){
_start:
{
lean_object* v___x_4137_; 
v___x_4137_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11___redArg(v_msgData_4132_, v_macroStack_4133_, v___y_4135_);
return v___x_4137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11___boxed(lean_object* v_msgData_4138_, lean_object* v_macroStack_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_){
_start:
{
lean_object* v_res_4143_; 
v_res_4143_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11(v_msgData_4138_, v_macroStack_4139_, v___y_4140_, v___y_4141_);
lean_dec(v___y_4141_);
lean_dec_ref(v___y_4140_);
return v_res_4143_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1___redArg(lean_object* v_declName_4144_, lean_object* v___y_4145_){
_start:
{
lean_object* v___x_4147_; lean_object* v_env_4148_; uint8_t v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
v___x_4147_ = lean_st_ref_get(v___y_4145_);
v_env_4148_ = lean_ctor_get(v___x_4147_, 0);
lean_inc_ref(v_env_4148_);
lean_dec(v___x_4147_);
v___x_4149_ = l_Lean_isInductiveCore(v_env_4148_, v_declName_4144_);
v___x_4150_ = lean_box(v___x_4149_);
v___x_4151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4150_);
return v___x_4151_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1___redArg___boxed(lean_object* v_declName_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_){
_start:
{
lean_object* v_res_4155_; 
v_res_4155_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1___redArg(v_declName_4152_, v___y_4153_);
lean_dec(v___y_4153_);
return v_res_4155_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1(lean_object* v_declName_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_){
_start:
{
lean_object* v___x_4160_; 
v___x_4160_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1___redArg(v_declName_4156_, v___y_4158_);
return v___x_4160_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1___boxed(lean_object* v_declName_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_){
_start:
{
lean_object* v_res_4165_; 
v_res_4165_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1(v_declName_4161_, v___y_4162_, v___y_4163_);
lean_dec(v___y_4163_);
lean_dec_ref(v___y_4162_);
return v_res_4165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___lam__0(uint8_t v_____do__lift_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_){
_start:
{
if (v_____do__lift_4166_ == 0)
{
uint8_t v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; 
v___x_4170_ = 1;
v___x_4171_ = lean_box(v___x_4170_);
v___x_4172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4172_, 0, v___x_4171_);
return v___x_4172_;
}
else
{
uint8_t v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; 
v___x_4173_ = 0;
v___x_4174_ = lean_box(v___x_4173_);
v___x_4175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4174_);
return v___x_4175_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_){
_start:
{
uint8_t v_____do__lift_1654__boxed_4180_; lean_object* v_res_4181_; 
v_____do__lift_1654__boxed_4180_ = lean_unbox(v_____do__lift_4176_);
v_res_4181_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___lam__0(v_____do__lift_1654__boxed_4180_, v___y_4177_, v___y_4178_);
lean_dec(v___y_4178_);
lean_dec_ref(v___y_4177_);
return v_res_4181_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__2(lean_object* v_as_4182_, size_t v_i_4183_, size_t v_stop_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_){
_start:
{
uint8_t v___x_4192_; 
v___x_4192_ = lean_usize_dec_eq(v_i_4183_, v_stop_4184_);
if (v___x_4192_ == 0)
{
uint8_t v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; 
v___x_4193_ = 1;
v___x_4194_ = lean_array_uget_borrowed(v_as_4182_, v_i_4183_);
lean_inc(v___x_4194_);
v___x_4195_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1___redArg(v___x_4194_, v___y_4186_);
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_object* v_a_4196_; lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4205_; 
v_a_4196_ = lean_ctor_get(v___x_4195_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_4195_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4198_ = v___x_4195_;
v_isShared_4199_ = v_isSharedCheck_4205_;
goto v_resetjp_4197_;
}
else
{
lean_inc(v_a_4196_);
lean_dec(v___x_4195_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4205_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
uint8_t v___x_4200_; 
v___x_4200_ = lean_unbox(v_a_4196_);
lean_dec(v_a_4196_);
if (v___x_4200_ == 0)
{
lean_object* v___x_4201_; lean_object* v___x_4203_; 
v___x_4201_ = lean_box(v___x_4193_);
if (v_isShared_4199_ == 0)
{
lean_ctor_set(v___x_4198_, 0, v___x_4201_);
v___x_4203_ = v___x_4198_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v___x_4201_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
return v___x_4203_;
}
}
else
{
lean_del_object(v___x_4198_);
goto v___jp_4188_;
}
}
}
else
{
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_object* v_a_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4215_; 
v_a_4206_ = lean_ctor_get(v___x_4195_, 0);
v_isSharedCheck_4215_ = !lean_is_exclusive(v___x_4195_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4208_ = v___x_4195_;
v_isShared_4209_ = v_isSharedCheck_4215_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_a_4206_);
lean_dec(v___x_4195_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4215_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
uint8_t v___x_4210_; 
v___x_4210_ = lean_unbox(v_a_4206_);
lean_dec(v_a_4206_);
if (v___x_4210_ == 0)
{
lean_del_object(v___x_4208_);
goto v___jp_4188_;
}
else
{
lean_object* v___x_4211_; lean_object* v___x_4213_; 
v___x_4211_ = lean_box(v___x_4193_);
if (v_isShared_4209_ == 0)
{
lean_ctor_set_tag(v___x_4208_, 0);
lean_ctor_set(v___x_4208_, 0, v___x_4211_);
v___x_4213_ = v___x_4208_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v___x_4211_);
v___x_4213_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
return v___x_4213_;
}
}
}
}
else
{
return v___x_4195_;
}
}
}
else
{
uint8_t v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; 
v___x_4216_ = 0;
v___x_4217_ = lean_box(v___x_4216_);
v___x_4218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4218_, 0, v___x_4217_);
return v___x_4218_;
}
v___jp_4188_:
{
size_t v___x_4189_; size_t v___x_4190_; 
v___x_4189_ = ((size_t)1ULL);
v___x_4190_ = lean_usize_add(v_i_4183_, v___x_4189_);
v_i_4183_ = v___x_4190_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__2___boxed(lean_object* v_as_4219_, lean_object* v_i_4220_, lean_object* v_stop_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_){
_start:
{
size_t v_i_boxed_4225_; size_t v_stop_boxed_4226_; lean_object* v_res_4227_; 
v_i_boxed_4225_ = lean_unbox_usize(v_i_4220_);
lean_dec(v_i_4220_);
v_stop_boxed_4226_ = lean_unbox_usize(v_stop_4221_);
lean_dec(v_stop_4221_);
v_res_4227_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__2(v_as_4219_, v_i_boxed_4225_, v_stop_boxed_4226_, v___y_4222_, v___y_4223_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
lean_dec_ref(v_as_4219_);
return v_res_4227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__0(lean_object* v_as_4228_, size_t v_sz_4229_, size_t v_i_4230_, lean_object* v_b_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_){
_start:
{
uint8_t v___x_4235_; 
v___x_4235_ = lean_usize_dec_lt(v_i_4230_, v_sz_4229_);
if (v___x_4235_ == 0)
{
lean_object* v___x_4236_; 
v___x_4236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4236_, 0, v_b_4231_);
return v___x_4236_;
}
else
{
lean_object* v___x_4237_; lean_object* v_a_4238_; lean_object* v___x_4239_; 
v___x_4237_ = lean_box(0);
v_a_4238_ = lean_array_uget_borrowed(v_as_4228_, v_i_4230_);
lean_inc(v_a_4238_);
v___x_4239_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance(v_a_4238_, v___y_4232_, v___y_4233_);
if (lean_obj_tag(v___x_4239_) == 0)
{
size_t v___x_4240_; size_t v___x_4241_; 
lean_dec_ref_known(v___x_4239_, 1);
v___x_4240_ = ((size_t)1ULL);
v___x_4241_ = lean_usize_add(v_i_4230_, v___x_4240_);
v_i_4230_ = v___x_4241_;
v_b_4231_ = v___x_4237_;
goto _start;
}
else
{
return v___x_4239_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__0___boxed(lean_object* v_as_4243_, lean_object* v_sz_4244_, lean_object* v_i_4245_, lean_object* v_b_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_){
_start:
{
size_t v_sz_boxed_4250_; size_t v_i_boxed_4251_; lean_object* v_res_4252_; 
v_sz_boxed_4250_ = lean_unbox_usize(v_sz_4244_);
lean_dec(v_sz_4244_);
v_i_boxed_4251_ = lean_unbox_usize(v_i_4245_);
lean_dec(v_i_4245_);
v_res_4252_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__0(v_as_4243_, v_sz_boxed_4250_, v_i_boxed_4251_, v_b_4246_, v___y_4247_, v___y_4248_);
lean_dec(v___y_4248_);
lean_dec_ref(v___y_4247_);
lean_dec_ref(v_as_4243_);
return v_res_4252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler(lean_object* v_declNames_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_){
_start:
{
lean_object* v___y_4281_; lean_object* v___x_4284_; lean_object* v___x_4285_; uint8_t v___x_4286_; 
v___x_4284_ = lean_unsigned_to_nat(0u);
v___x_4285_ = lean_array_get_size(v_declNames_4253_);
v___x_4286_ = lean_nat_dec_lt(v___x_4284_, v___x_4285_);
if (v___x_4286_ == 0)
{
lean_object* v___x_4287_; 
v___x_4287_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___lam__0(v___x_4286_, v_a_4254_, v_a_4255_);
v___y_4281_ = v___x_4287_;
goto v___jp_4280_;
}
else
{
if (v___x_4286_ == 0)
{
goto v___jp_4257_;
}
else
{
size_t v___x_4288_; size_t v___x_4289_; lean_object* v___x_4290_; 
v___x_4288_ = ((size_t)0ULL);
v___x_4289_ = lean_usize_of_nat(v___x_4285_);
v___x_4290_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__2(v_declNames_4253_, v___x_4288_, v___x_4289_, v_a_4254_, v_a_4255_);
if (lean_obj_tag(v___x_4290_) == 0)
{
lean_object* v_a_4291_; uint8_t v___x_4292_; lean_object* v___x_4293_; 
v_a_4291_ = lean_ctor_get(v___x_4290_, 0);
lean_inc(v_a_4291_);
lean_dec_ref_known(v___x_4290_, 1);
v___x_4292_ = lean_unbox(v_a_4291_);
lean_dec(v_a_4291_);
v___x_4293_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___lam__0(v___x_4292_, v_a_4254_, v_a_4255_);
v___y_4281_ = v___x_4293_;
goto v___jp_4280_;
}
else
{
v___y_4281_ = v___x_4290_;
goto v___jp_4280_;
}
}
}
v___jp_4257_:
{
uint8_t v___x_4258_; lean_object* v___x_4259_; size_t v_sz_4260_; size_t v___x_4261_; lean_object* v___x_4262_; 
v___x_4258_ = 1;
v___x_4259_ = lean_box(0);
v_sz_4260_ = lean_array_size(v_declNames_4253_);
v___x_4261_ = ((size_t)0ULL);
v___x_4262_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__0(v_declNames_4253_, v_sz_4260_, v___x_4261_, v___x_4259_, v_a_4254_, v_a_4255_);
if (lean_obj_tag(v___x_4262_) == 0)
{
lean_object* v___x_4264_; uint8_t v_isShared_4265_; uint8_t v_isSharedCheck_4270_; 
v_isSharedCheck_4270_ = !lean_is_exclusive(v___x_4262_);
if (v_isSharedCheck_4270_ == 0)
{
lean_object* v_unused_4271_; 
v_unused_4271_ = lean_ctor_get(v___x_4262_, 0);
lean_dec(v_unused_4271_);
v___x_4264_ = v___x_4262_;
v_isShared_4265_ = v_isSharedCheck_4270_;
goto v_resetjp_4263_;
}
else
{
lean_dec(v___x_4262_);
v___x_4264_ = lean_box(0);
v_isShared_4265_ = v_isSharedCheck_4270_;
goto v_resetjp_4263_;
}
v_resetjp_4263_:
{
lean_object* v___x_4266_; lean_object* v___x_4268_; 
v___x_4266_ = lean_box(v___x_4258_);
if (v_isShared_4265_ == 0)
{
lean_ctor_set(v___x_4264_, 0, v___x_4266_);
v___x_4268_ = v___x_4264_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v___x_4266_);
v___x_4268_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
return v___x_4268_;
}
}
}
else
{
lean_object* v_a_4272_; lean_object* v___x_4274_; uint8_t v_isShared_4275_; uint8_t v_isSharedCheck_4279_; 
v_a_4272_ = lean_ctor_get(v___x_4262_, 0);
v_isSharedCheck_4279_ = !lean_is_exclusive(v___x_4262_);
if (v_isSharedCheck_4279_ == 0)
{
v___x_4274_ = v___x_4262_;
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
else
{
lean_inc(v_a_4272_);
lean_dec(v___x_4262_);
v___x_4274_ = lean_box(0);
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
v_resetjp_4273_:
{
lean_object* v___x_4277_; 
if (v_isShared_4275_ == 0)
{
v___x_4277_ = v___x_4274_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v_a_4272_);
v___x_4277_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
return v___x_4277_;
}
}
}
}
v___jp_4280_:
{
if (lean_obj_tag(v___y_4281_) == 0)
{
lean_object* v_a_4282_; uint8_t v___x_4283_; 
v_a_4282_ = lean_ctor_get(v___y_4281_, 0);
v___x_4283_ = lean_unbox(v_a_4282_);
if (v___x_4283_ == 0)
{
return v___y_4281_;
}
else
{
lean_dec_ref_known(v___y_4281_, 1);
goto v___jp_4257_;
}
}
else
{
return v___y_4281_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___boxed(lean_object* v_declNames_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_){
_start:
{
lean_object* v_res_4298_; 
v_res_4298_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler(v_declNames_4294_, v_a_4295_, v_a_4296_);
lean_dec(v_a_4296_);
lean_dec_ref(v_a_4295_);
lean_dec_ref(v_declNames_4294_);
return v_res_4298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; 
v___x_4347_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader___closed__0));
v___x_4348_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__0_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_));
v___x_4349_ = l_Lean_Elab_registerDerivingHandler(v___x_4347_, v___x_4348_);
if (lean_obj_tag(v___x_4349_) == 0)
{
lean_object* v___x_4350_; uint8_t v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; 
lean_dec_ref_known(v___x_4349_, 1);
v___x_4350_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__0));
v___x_4351_ = 0;
v___x_4352_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__18_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_));
v___x_4353_ = l_Lean_registerTraceClass(v___x_4350_, v___x_4351_, v___x_4352_);
return v___x_4353_;
}
else
{
return v___x_4349_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2____boxed(lean_object* v_a_4354_){
_start:
{
lean_object* v_res_4355_; 
v_res_4355_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_();
return v_res_4355_;
}
}
lean_object* runtime_initialize_Lean_Data_Options(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CasesOnSameCtor(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SameCtorUtils(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_OfFn(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Deriving_Ord(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CasesOnSameCtor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_SameCtorUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_OfFn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Deriving_Ord_0__initFn_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Elab_Deriving_Ord_0__deriving_ord_linear__construction__threshold = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Elab_Deriving_Ord_0__deriving_ord_linear__construction__threshold);
lean_dec_ref(res);
res = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Deriving_Ord(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Options(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Deriving_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CasesOnSameCtor(uint8_t builtin);
lean_object* initialize_Lean_Meta_SameCtorUtils(uint8_t builtin);
lean_object* initialize_Init_Data_Array_OfFn(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Deriving_Ord(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Deriving_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CasesOnSameCtor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SameCtorUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_OfFn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Deriving_Ord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Deriving_Ord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Deriving_Ord(builtin);
}
#ifdef __cplusplus
}
#endif
