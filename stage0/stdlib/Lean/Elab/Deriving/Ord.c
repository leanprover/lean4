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
lean_object* l_Array_mkArray0(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
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
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Deriving_mkDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Core_betaReduce(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_occursOrInType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
lean_object* l_Lean_mkCtorIdxName(lean_object*);
lean_object* l_Lean_mkCasesOnSameCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Ordering.eq"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__0_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "eq"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__2_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(226, 44, 125, 228, 251, 150, 72, 72)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 150, 86, 2, 28, 163, 164, 77)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__4 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__4_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__5 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__5_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__6 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__6_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__4_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__6_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__7 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__7_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "@"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__8 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__8_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "explicit"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__9 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__9_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__10_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__10_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__10_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__9_value),LEAN_SCALAR_PTR_LITERAL(141, 201, 75, 195, 250, 223, 114, 184)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__10 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__10_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__12 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__12_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__13 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__13_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__14;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__15 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__15_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(226, 44, 125, 228, 251, 150, 72, 72)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__16_value_aux_0),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__15_value),LEAN_SCALAR_PTR_LITERAL(151, 65, 236, 10, 147, 23, 177, 156)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__16 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__16_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__17 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__17_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__18 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__18_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Ordering.lt"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__19 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__19_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__20;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__16_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__21 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__21_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__21_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__22 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__22_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__18_value),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__22_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__23 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__23_value;
static const lean_string_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__24 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__24_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__8_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__25_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__25_value_aux_1),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__25_value_aux_2),((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__24_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
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
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__17 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__21_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__18 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__17_value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__18_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__19 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__19_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__29_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__20 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__31_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__21 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__21_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__20_value),((lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__21_value)}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__22 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__22_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__23 = (const lean_object*)&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__23_value;
static const lean_ctor_object l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
uint8_t v___x_49186__boxed_361_; lean_object* v_res_362_; 
v___x_49186__boxed_361_ = lean_unbox(v___x_349_);
v_res_362_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0(v___x_49186__boxed_361_, v___x_350_, v___x_351_, v_snd_352_, v_rhs_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
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
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_401_ = l_Lean_instInhabitedExpr;
v___x_402_ = lean_nat_add(v___x_384_, v_a_387_);
v___x_403_ = lean_array_get_borrowed(v___x_401_, v_xs_385_, v___x_402_);
lean_dec(v___x_402_);
lean_inc(v___x_403_);
v___x_404_ = l_Lean_Meta_isProof(v___x_403_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v_snd_405_; lean_object* v_a_406_; uint8_t v___x_407_; 
v_snd_405_ = lean_ctor_get(v_b_388_, 1);
lean_inc(v_snd_405_);
v_a_406_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_a_406_);
lean_dec_ref_known(v___x_404_, 1);
v___x_407_ = lean_unbox(v_a_406_);
if (v___x_407_ == 0)
{
lean_object* v_fst_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_483_; 
v_fst_408_ = lean_ctor_get(v_b_388_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v_b_388_);
if (v_isSharedCheck_483_ == 0)
{
lean_object* v_unused_484_; 
v_unused_484_ = lean_ctor_get(v_b_388_, 1);
lean_dec(v_unused_484_);
v___x_410_ = v_b_388_;
v_isShared_411_ = v_isSharedCheck_483_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_fst_408_);
lean_dec(v_b_388_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_483_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v_fst_412_; lean_object* v_snd_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_482_; 
v_fst_412_ = lean_ctor_get(v_snd_405_, 0);
v_snd_413_ = lean_ctor_get(v_snd_405_, 1);
v_isSharedCheck_482_ = !lean_is_exclusive(v_snd_405_);
if (v_isSharedCheck_482_ == 0)
{
v___x_415_ = v_snd_405_;
v_isShared_416_ = v_isSharedCheck_482_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_snd_413_);
lean_inc(v_fst_412_);
lean_dec(v_snd_405_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_482_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v_lctx_417_; uint8_t v___x_418_; 
v_lctx_417_ = lean_ctor_get(v___y_389_, 2);
lean_inc(v___x_403_);
lean_inc_ref(v_lctx_417_);
v___x_418_ = l_Lean_Meta_occursOrInType(v_lctx_417_, v___x_403_, v_a_386_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; lean_object* v___x_420_; 
lean_dec(v_a_406_);
v___x_419_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__1));
v___x_420_ = l_Lean_Core_mkFreshUserName(v___x_419_, v___y_391_, v___y_392_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v_a_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v_a_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_a_421_);
lean_dec_ref_known(v___x_420_, 1);
v___x_422_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__3));
v___x_423_ = l_Lean_Core_mkFreshUserName(v___x_422_, v___y_391_, v___y_392_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___f_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_432_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_a_424_);
lean_dec_ref_known(v___x_423_, 1);
v___x_425_ = l_Lean_mkIdent(v_a_421_);
v___x_426_ = l_Lean_mkIdent(v_a_424_);
v___x_427_ = lean_box(v___x_418_);
lean_inc(v___x_426_);
lean_inc(v___x_425_);
v___f_428_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_428_, 0, v___x_427_);
lean_closure_set(v___f_428_, 1, v___x_425_);
lean_closure_set(v___f_428_, 2, v___x_426_);
lean_closure_set(v___f_428_, 3, v_snd_413_);
v___x_429_ = lean_array_push(v_fst_408_, v___x_425_);
v___x_430_ = lean_array_push(v_fst_412_, v___x_426_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 1, v___f_428_);
lean_ctor_set(v___x_415_, 0, v___x_430_);
v___x_432_ = v___x_415_;
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
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 1, v___x_432_);
lean_ctor_set(v___x_410_, 0, v___x_429_);
v___x_434_ = v___x_410_;
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
lean_dec(v_a_421_);
lean_del_object(v___x_415_);
lean_dec(v_snd_413_);
lean_dec(v_fst_412_);
lean_del_object(v___x_410_);
lean_dec(v_fst_408_);
lean_dec(v_a_387_);
v_a_437_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v___x_423_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_423_);
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
lean_del_object(v___x_415_);
lean_dec(v_snd_413_);
lean_dec(v_fst_412_);
lean_del_object(v___x_410_);
lean_dec(v_fst_408_);
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
v___x_458_ = lean_array_push(v_fst_408_, v___x_457_);
v___x_459_ = lean_unbox(v_a_406_);
lean_dec(v_a_406_);
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
v___x_467_ = lean_array_push(v_fst_412_, v___x_466_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 0, v___x_467_);
v___x_469_ = v___x_415_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_snd_413_);
v___x_469_ = v_reuseFailAlloc_473_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_471_; 
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 1, v___x_469_);
lean_ctor_set(v___x_410_, 0, v___x_458_);
v___x_471_ = v___x_410_;
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
lean_del_object(v___x_415_);
lean_dec(v_snd_413_);
lean_dec(v_fst_412_);
lean_del_object(v___x_410_);
lean_dec(v_fst_408_);
lean_dec(v_a_406_);
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
}
}
else
{
lean_object* v_fst_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_510_; 
lean_dec(v_a_406_);
v_fst_485_ = lean_ctor_get(v_b_388_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v_b_388_);
if (v_isSharedCheck_510_ == 0)
{
lean_object* v_unused_511_; 
v_unused_511_ = lean_ctor_get(v_b_388_, 1);
lean_dec(v_unused_511_);
v___x_487_ = v_b_388_;
v_isShared_488_ = v_isSharedCheck_510_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_fst_485_);
lean_dec(v_b_388_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_510_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v_fst_489_; lean_object* v_snd_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_509_; 
v_fst_489_ = lean_ctor_get(v_snd_405_, 0);
v_snd_490_ = lean_ctor_get(v_snd_405_, 1);
v_isSharedCheck_509_ = !lean_is_exclusive(v_snd_405_);
if (v_isSharedCheck_509_ == 0)
{
v___x_492_ = v_snd_405_;
v_isShared_493_ = v_isSharedCheck_509_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_snd_490_);
lean_inc(v_fst_489_);
lean_dec(v_snd_405_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_509_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v_ref_494_; uint8_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_504_; 
v_ref_494_ = lean_ctor_get(v___y_391_, 2);
v___x_495_ = 0;
v___x_496_ = l_Lean_SourceInfo_fromRef(v_ref_494_, v___x_495_);
v___x_497_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8));
v___x_498_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__9));
lean_inc(v___x_496_);
v___x_499_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_496_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
v___x_500_ = l_Lean_Syntax_node1(v___x_496_, v___x_497_, v___x_499_);
lean_inc(v___x_500_);
v___x_501_ = lean_array_push(v_fst_485_, v___x_500_);
v___x_502_ = lean_array_push(v_fst_489_, v___x_500_);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v___x_502_);
v___x_504_ = v___x_492_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_502_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v_snd_490_);
v___x_504_ = v_reuseFailAlloc_508_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_506_; 
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 1, v___x_504_);
lean_ctor_set(v___x_487_, 0, v___x_501_);
v___x_506_ = v___x_487_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_501_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
v_a_395_ = v___x_506_;
goto v___jp_394_;
}
}
}
}
}
}
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
lean_dec_ref(v_b_388_);
lean_dec(v_a_387_);
v_a_512_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_404_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_404_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___boxed(lean_object* v_upperBound_520_, lean_object* v___x_521_, lean_object* v_xs_522_, lean_object* v_a_523_, lean_object* v_a_524_, lean_object* v_b_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg(v_upperBound_520_, v___x_521_, v_xs_522_, v_a_523_, v_a_524_, v_b_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec_ref(v_a_523_);
lean_dec_ref(v_xs_522_);
lean_dec(v___x_521_);
lean_dec(v_upperBound_520_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4___redArg(lean_object* v_upperBound_532_, lean_object* v_a_533_, lean_object* v_b_534_, lean_object* v___y_535_){
_start:
{
uint8_t v___x_537_; 
v___x_537_ = lean_nat_dec_lt(v_a_533_, v_upperBound_532_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; 
lean_dec(v_a_533_);
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v_b_534_);
return v___x_538_;
}
else
{
lean_object* v_ref_539_; uint8_t v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v_ref_539_ = lean_ctor_get(v___y_535_, 2);
v___x_540_ = 0;
v___x_541_ = l_Lean_SourceInfo_fromRef(v_ref_539_, v___x_540_);
v___x_542_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8));
v___x_543_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__9));
lean_inc(v___x_541_);
v___x_544_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_541_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
v___x_545_ = l_Lean_Syntax_node1(v___x_541_, v___x_542_, v___x_544_);
v___x_546_ = lean_array_push(v_b_534_, v___x_545_);
v___x_547_ = lean_unsigned_to_nat(1u);
v___x_548_ = lean_nat_add(v_a_533_, v___x_547_);
lean_dec(v_a_533_);
v_a_533_ = v___x_548_;
v_b_534_ = v___x_546_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4___redArg___boxed(lean_object* v_upperBound_550_, lean_object* v_a_551_, lean_object* v_b_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4___redArg(v_upperBound_550_, v_a_551_, v_b_552_, v___y_553_);
lean_dec_ref(v___y_553_);
lean_dec(v_upperBound_550_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3___redArg(lean_object* v_upperBound_556_, lean_object* v_a_557_, lean_object* v_b_558_, lean_object* v___y_559_){
_start:
{
uint8_t v___x_561_; 
v___x_561_ = lean_nat_dec_lt(v_a_557_, v_upperBound_556_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; 
lean_dec(v_a_557_);
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v_b_558_);
return v___x_562_;
}
else
{
lean_object* v_fst_563_; lean_object* v_snd_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_583_; 
v_fst_563_ = lean_ctor_get(v_b_558_, 0);
v_snd_564_ = lean_ctor_get(v_b_558_, 1);
v_isSharedCheck_583_ = !lean_is_exclusive(v_b_558_);
if (v_isSharedCheck_583_ == 0)
{
v___x_566_ = v_b_558_;
v_isShared_567_ = v_isSharedCheck_583_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_snd_564_);
lean_inc(v_fst_563_);
lean_dec(v_b_558_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_583_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v_ref_568_; uint8_t v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_578_; 
v_ref_568_ = lean_ctor_get(v___y_559_, 2);
v___x_569_ = 0;
v___x_570_ = l_Lean_SourceInfo_fromRef(v_ref_568_, v___x_569_);
v___x_571_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8));
v___x_572_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__9));
lean_inc(v___x_570_);
v___x_573_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_570_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v___x_574_ = l_Lean_Syntax_node1(v___x_570_, v___x_571_, v___x_573_);
lean_inc(v___x_574_);
v___x_575_ = lean_array_push(v_fst_563_, v___x_574_);
v___x_576_ = lean_array_push(v_snd_564_, v___x_574_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 1, v___x_576_);
lean_ctor_set(v___x_566_, 0, v___x_575_);
v___x_578_ = v___x_566_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_575_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v___x_576_);
v___x_578_ = v_reuseFailAlloc_582_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = lean_unsigned_to_nat(1u);
v___x_580_ = lean_nat_add(v_a_557_, v___x_579_);
lean_dec(v_a_557_);
v_a_557_ = v___x_580_;
v_b_558_ = v___x_578_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3___redArg___boxed(lean_object* v_upperBound_584_, lean_object* v_a_585_, lean_object* v_b_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3___redArg(v_upperBound_584_, v_a_585_, v_b_586_, v___y_587_);
lean_dec_ref(v___y_587_);
lean_dec(v_upperBound_584_);
return v_res_589_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__0));
v___x_592_ = l_String_toRawSubstring_x27(v___x_591_);
return v___x_592_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11(void){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_Array_mkArray0(lean_box(0));
return v___x_615_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__14(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__13));
v___x_619_ = l_Lean_mkAtom(v___x_618_);
return v___x_619_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__20(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_629_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__19));
v___x_630_ = l_String_toRawSubstring_x27(v___x_629_);
return v___x_630_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__27(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__26));
v___x_647_ = l_String_toRawSubstring_x27(v___x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2(lean_object* v_indVal_663_, lean_object* v___x_664_, lean_object* v_alts_665_, lean_object* v___f_666_, lean_object* v_numFields_667_, lean_object* v___f_668_, lean_object* v_head_669_, lean_object* v_xs_670_, lean_object* v_type_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_Core_betaReduce(v_type_671_, v___y_676_, v___y_677_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; lean_object* v_numParams_681_; lean_object* v_numIndices_682_; lean_object* v___x_683_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_a_680_);
lean_dec_ref_known(v___x_679_, 1);
v_numParams_681_ = lean_ctor_get(v_indVal_663_, 1);
v_numIndices_682_ = lean_ctor_get(v_indVal_663_, 2);
lean_inc_ref(v_alts_665_);
lean_inc(v___x_664_);
v___x_683_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4___redArg(v_numIndices_682_, v___x_664_, v_alts_665_, v___y_676_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_a_684_);
lean_dec_ref_known(v___x_683_, 1);
lean_inc_ref(v_alts_665_);
v___x_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_685_, 0, v_alts_665_);
lean_ctor_set(v___x_685_, 1, v_alts_665_);
lean_inc(v___x_664_);
v___x_686_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3___redArg(v_numParams_681_, v___x_664_, v___x_685_, v___y_676_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v_fst_688_; lean_object* v_snd_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_901_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_687_);
lean_dec_ref_known(v___x_686_, 1);
v_fst_688_ = lean_ctor_get(v_a_687_, 0);
v_snd_689_ = lean_ctor_get(v_a_687_, 1);
v_isSharedCheck_901_ = !lean_is_exclusive(v_a_687_);
if (v_isSharedCheck_901_ == 0)
{
v___x_691_ = v_a_687_;
v_isShared_692_ = v_isSharedCheck_901_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_snd_689_);
lean_inc(v_fst_688_);
lean_dec(v_a_687_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_901_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
lean_ctor_set(v___x_691_, 1, v___f_666_);
lean_ctor_set(v___x_691_, 0, v_snd_689_);
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_snd_689_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v___f_666_);
v___x_694_ = v_reuseFailAlloc_900_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_695_, 0, v_fst_688_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
v___x_696_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg(v_numFields_667_, v_numParams_681_, v_xs_670_, v_a_680_, v___x_664_, v___x_695_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
lean_dec(v_a_680_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; lean_object* v_toCold_698_; lean_object* v_ref_699_; lean_object* v___x_700_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_a_697_);
lean_dec_ref_known(v___x_696_, 1);
v_toCold_698_ = lean_ctor_get(v___y_676_, 0);
v_ref_699_ = lean_ctor_get(v___y_676_, 2);
lean_inc_ref(v___f_668_);
lean_inc(v___y_677_);
lean_inc_ref(v___y_676_);
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
lean_inc(v___y_673_);
lean_inc_ref(v___y_672_);
v___x_700_ = lean_apply_7(v___f_668_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, lean_box(0));
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_702_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_a_701_);
lean_dec_ref_known(v___x_700_, 1);
lean_inc_ref(v___f_668_);
lean_inc(v___y_677_);
lean_inc_ref(v___y_676_);
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
lean_inc(v___y_673_);
lean_inc_ref(v___y_672_);
v___x_702_ = lean_apply_7(v___f_668_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, lean_box(0));
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_704_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
lean_dec_ref_known(v___x_702_, 1);
lean_inc_ref(v___f_668_);
lean_inc(v___y_677_);
lean_inc_ref(v___y_676_);
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
lean_inc(v___y_673_);
lean_inc_ref(v___y_672_);
v___x_704_ = lean_apply_7(v___f_668_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, lean_box(0));
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v___x_706_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_705_);
lean_dec_ref_known(v___x_704_, 1);
lean_inc_ref(v___f_668_);
lean_inc(v___y_677_);
lean_inc_ref(v___y_676_);
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
lean_inc(v___y_673_);
lean_inc_ref(v___y_672_);
v___x_706_ = lean_apply_7(v___f_668_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, lean_box(0));
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_snd_707_; lean_object* v_a_708_; lean_object* v_fst_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_858_; 
v_snd_707_ = lean_ctor_get(v_a_697_, 1);
lean_inc(v_snd_707_);
v_a_708_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_708_);
lean_dec_ref_known(v___x_706_, 1);
v_fst_709_ = lean_ctor_get(v_a_697_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v_a_697_);
if (v_isSharedCheck_858_ == 0)
{
lean_object* v_unused_859_; 
v_unused_859_ = lean_ctor_get(v_a_697_, 1);
lean_dec(v_unused_859_);
v___x_711_ = v_a_697_;
v_isShared_712_ = v_isSharedCheck_858_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_fst_709_);
lean_dec(v_a_697_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_858_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v_fst_713_; lean_object* v_snd_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_857_; 
v_fst_713_ = lean_ctor_get(v_snd_707_, 0);
v_snd_714_ = lean_ctor_get(v_snd_707_, 1);
v_isSharedCheck_857_ = !lean_is_exclusive(v_snd_707_);
if (v_isSharedCheck_857_ == 0)
{
v___x_716_ = v_snd_707_;
v_isShared_717_ = v_isSharedCheck_857_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_snd_714_);
lean_inc(v_fst_713_);
lean_dec(v_snd_707_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_857_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v_quotContext_718_; lean_object* v_currMacroScope_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v_quotContext_718_ = lean_ctor_get(v_toCold_698_, 8);
v_currMacroScope_719_ = lean_ctor_get(v_toCold_698_, 9);
v___x_720_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1);
v___x_721_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3));
lean_inc(v_currMacroScope_719_);
lean_inc(v_quotContext_718_);
v___x_722_ = l_Lean_addMacroScope(v_quotContext_718_, v___x_721_, v_currMacroScope_719_);
v___x_723_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__7));
v___x_724_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_724_, 0, v_a_708_);
lean_ctor_set(v___x_724_, 1, v___x_720_);
lean_ctor_set(v___x_724_, 2, v___x_722_);
lean_ctor_set(v___x_724_, 3, v___x_723_);
lean_inc(v___y_677_);
lean_inc_ref(v___y_676_);
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
lean_inc(v___y_673_);
lean_inc_ref(v___y_672_);
v___x_725_ = lean_apply_8(v_snd_714_, v___x_724_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, lean_box(0));
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_a_726_; lean_object* v___x_727_; 
v_a_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v___x_725_, 1);
lean_inc_ref(v___f_668_);
lean_inc(v___y_677_);
lean_inc_ref(v___y_676_);
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
lean_inc(v___y_673_);
lean_inc_ref(v___y_672_);
v___x_727_ = lean_apply_7(v___f_668_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, lean_box(0));
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v_a_728_; lean_object* v___x_729_; 
v_a_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_a_728_);
lean_dec_ref_known(v___x_727_, 1);
lean_inc_ref(v___f_668_);
lean_inc(v___y_677_);
lean_inc_ref(v___y_676_);
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
lean_inc(v___y_673_);
lean_inc_ref(v___y_672_);
v___x_729_ = lean_apply_7(v___f_668_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, lean_box(0));
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v___x_731_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
lean_dec_ref_known(v___x_729_, 1);
lean_inc(v___y_677_);
lean_inc_ref(v___y_676_);
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
lean_inc(v___y_673_);
lean_inc_ref(v___y_672_);
v___x_731_ = lean_apply_7(v___f_668_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, lean_box(0));
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_824_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_824_ == 0)
{
v___x_734_ = v___x_731_;
v_isShared_735_ = v_isSharedCheck_824_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_731_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_824_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
uint8_t v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_740_; 
v___x_736_ = 0;
v___x_737_ = l_Lean_SourceInfo_fromRef(v_ref_699_, v___x_736_);
v___x_738_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__8));
lean_inc(v___x_737_);
if (v_isShared_717_ == 0)
{
lean_ctor_set_tag(v___x_716_, 2);
lean_ctor_set(v___x_716_, 1, v___x_738_);
lean_ctor_set(v___x_716_, 0, v___x_737_);
v___x_740_ = v___x_716_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v___x_738_);
v___x_740_ = v_reuseFailAlloc_823_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_744_; 
v___x_741_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3));
v___x_742_ = l_Lean_mkIdent(v_head_669_);
lean_inc(v_a_701_);
if (v_isShared_712_ == 0)
{
lean_ctor_set_tag(v___x_711_, 2);
lean_ctor_set(v___x_711_, 1, v___x_738_);
lean_ctor_set(v___x_711_, 0, v_a_701_);
v___x_744_ = v___x_711_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_701_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v___x_738_);
v___x_744_ = v_reuseFailAlloc_822_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; size_t v_sz_769_; lean_object* v___x_770_; size_t v_sz_771_; size_t v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; size_t v_sz_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_820_; 
v___x_745_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__10));
lean_inc(v___x_742_);
lean_inc_n(v___x_737_, 2);
v___x_746_ = l_Lean_Syntax_node2(v___x_737_, v___x_745_, v___x_740_, v___x_742_);
lean_inc_n(v_a_701_, 2);
v___x_747_ = l_Lean_Syntax_node2(v_a_701_, v___x_745_, v___x_744_, v___x_742_);
v___x_748_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_749_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11);
v___x_750_ = l_Array_append___redArg(v___x_749_, v_fst_709_);
lean_dec(v_fst_709_);
v___x_751_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_751_, 0, v___x_737_);
lean_ctor_set(v___x_751_, 1, v___x_748_);
lean_ctor_set(v___x_751_, 2, v___x_750_);
v___x_752_ = l_Array_append___redArg(v___x_749_, v_fst_713_);
lean_dec(v_fst_713_);
v___x_753_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_753_, 0, v_a_701_);
lean_ctor_set(v___x_753_, 1, v___x_748_);
lean_ctor_set(v___x_753_, 2, v___x_752_);
v___x_754_ = l_Lean_Syntax_node2(v___x_737_, v___x_741_, v___x_746_, v___x_751_);
v___x_755_ = l_Lean_Syntax_node2(v_a_701_, v___x_741_, v___x_747_, v___x_753_);
v___x_756_ = lean_unsigned_to_nat(2u);
v___x_757_ = lean_mk_empty_array_with_capacity(v___x_756_);
lean_inc(v___x_754_);
lean_inc_ref(v___x_757_);
v___x_758_ = lean_array_push(v___x_757_, v___x_754_);
lean_inc_ref(v___x_758_);
v___x_759_ = lean_array_push(v___x_758_, v___x_755_);
lean_inc_n(v_a_684_, 2);
v___x_760_ = l_Array_append___redArg(v_a_684_, v___x_759_);
lean_dec_ref(v___x_759_);
v___x_761_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__9));
lean_inc(v_a_703_);
v___x_762_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_762_, 0, v_a_703_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8));
v___x_764_ = l_Lean_Syntax_node1(v_a_703_, v___x_763_, v___x_762_);
v___x_765_ = lean_array_push(v___x_758_, v___x_764_);
v___x_766_ = l_Array_append___redArg(v_a_684_, v___x_765_);
lean_dec_ref(v___x_765_);
v___x_767_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__12));
lean_inc_n(v_a_730_, 5);
v___x_768_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_768_, 0, v_a_730_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
v_sz_769_ = lean_array_size(v___x_766_);
lean_inc_n(v_a_728_, 4);
v___x_770_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_770_, 0, v_a_728_);
lean_ctor_set(v___x_770_, 1, v___x_767_);
v_sz_771_ = lean_array_size(v___x_760_);
v___x_772_ = ((size_t)0ULL);
v___x_773_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__1(v_sz_769_, v___x_772_, v___x_766_);
v___x_774_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__14, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__14_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__14);
v___x_775_ = l_Lean_mkSepArray(v___x_773_, v___x_774_);
lean_dec_ref(v___x_773_);
v___x_776_ = l_Array_append___redArg(v___x_749_, v___x_775_);
lean_dec_ref(v___x_775_);
v___x_777_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_777_, 0, v_a_730_);
lean_ctor_set(v___x_777_, 1, v___x_748_);
lean_ctor_set(v___x_777_, 2, v___x_776_);
v___x_778_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__1(v_sz_771_, v___x_772_, v___x_760_);
v___x_779_ = l_Lean_mkSepArray(v___x_778_, v___x_774_);
lean_dec_ref(v___x_778_);
v___x_780_ = l_Array_append___redArg(v___x_749_, v___x_779_);
lean_dec_ref(v___x_779_);
v___x_781_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_781_, 0, v_a_728_);
lean_ctor_set(v___x_781_, 1, v___x_748_);
lean_ctor_set(v___x_781_, 2, v___x_780_);
v___x_782_ = l_Lean_Syntax_node1(v_a_730_, v___x_748_, v___x_777_);
v___x_783_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__16));
lean_inc_n(v_currMacroScope_719_, 2);
lean_inc_n(v_quotContext_718_, 2);
v___x_784_ = l_Lean_addMacroScope(v_quotContext_718_, v___x_783_, v_currMacroScope_719_);
v___x_785_ = l_Lean_Syntax_node1(v_a_728_, v___x_748_, v___x_781_);
v___x_786_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__17));
v___x_787_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_787_, 0, v_a_730_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
lean_inc(v_a_705_);
v___x_788_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_788_, 0, v_a_705_);
lean_ctor_set(v___x_788_, 1, v___x_761_);
v___x_789_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_789_, 0, v_a_728_);
lean_ctor_set(v___x_789_, 1, v___x_786_);
v___x_790_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__20, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__20_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__20);
v___x_791_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__23));
v___x_792_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_792_, 0, v_a_730_);
lean_ctor_set(v___x_792_, 1, v___x_790_);
lean_ctor_set(v___x_792_, 2, v___x_784_);
lean_ctor_set(v___x_792_, 3, v___x_791_);
v___x_793_ = l_Lean_Syntax_node1(v_a_705_, v___x_763_, v___x_788_);
v___x_794_ = lean_array_push(v___x_757_, v___x_793_);
v___x_795_ = lean_array_push(v___x_794_, v___x_754_);
v___x_796_ = l_Array_append___redArg(v_a_684_, v___x_795_);
lean_dec_ref(v___x_795_);
v___x_797_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__25));
v___x_798_ = l_Lean_Syntax_node4(v_a_728_, v___x_797_, v___x_770_, v___x_785_, v___x_789_, v_a_726_);
v___x_799_ = l_Lean_Syntax_node4(v_a_730_, v___x_797_, v___x_768_, v___x_782_, v___x_787_, v___x_792_);
lean_inc_n(v_a_732_, 5);
v___x_800_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_800_, 0, v_a_732_);
lean_ctor_set(v___x_800_, 1, v___x_767_);
v_sz_801_ = lean_array_size(v___x_796_);
v___x_802_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__1(v_sz_801_, v___x_772_, v___x_796_);
v___x_803_ = l_Lean_mkSepArray(v___x_802_, v___x_774_);
lean_dec_ref(v___x_802_);
v___x_804_ = l_Array_append___redArg(v___x_749_, v___x_803_);
lean_dec_ref(v___x_803_);
v___x_805_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_805_, 0, v_a_732_);
lean_ctor_set(v___x_805_, 1, v___x_748_);
lean_ctor_set(v___x_805_, 2, v___x_804_);
v___x_806_ = l_Lean_Syntax_node1(v_a_732_, v___x_748_, v___x_805_);
v___x_807_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_807_, 0, v_a_732_);
lean_ctor_set(v___x_807_, 1, v___x_786_);
v___x_808_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__27, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__27_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__27);
v___x_809_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__29));
v___x_810_ = l_Lean_addMacroScope(v_quotContext_718_, v___x_809_, v_currMacroScope_719_);
v___x_811_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__33));
v___x_812_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_812_, 0, v_a_732_);
lean_ctor_set(v___x_812_, 1, v___x_808_);
lean_ctor_set(v___x_812_, 2, v___x_810_);
lean_ctor_set(v___x_812_, 3, v___x_811_);
v___x_813_ = l_Lean_Syntax_node4(v_a_732_, v___x_797_, v___x_800_, v___x_806_, v___x_807_, v___x_812_);
v___x_814_ = lean_unsigned_to_nat(3u);
v___x_815_ = lean_mk_empty_array_with_capacity(v___x_814_);
v___x_816_ = lean_array_push(v___x_815_, v___x_798_);
v___x_817_ = lean_array_push(v___x_816_, v___x_799_);
v___x_818_ = lean_array_push(v___x_817_, v___x_813_);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 0, v___x_818_);
v___x_820_ = v___x_734_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
}
else
{
lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_dec(v_a_730_);
lean_dec(v_a_728_);
lean_dec(v_a_726_);
lean_del_object(v___x_716_);
lean_dec(v_fst_713_);
lean_del_object(v___x_711_);
lean_dec(v_fst_709_);
lean_dec(v_a_705_);
lean_dec(v_a_703_);
lean_dec(v_a_701_);
lean_dec(v_a_684_);
lean_dec(v_head_669_);
v_a_825_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_731_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_731_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec(v_a_728_);
lean_dec(v_a_726_);
lean_del_object(v___x_716_);
lean_dec(v_fst_713_);
lean_del_object(v___x_711_);
lean_dec(v_fst_709_);
lean_dec(v_a_705_);
lean_dec(v_a_703_);
lean_dec(v_a_701_);
lean_dec(v_a_684_);
lean_dec(v_head_669_);
lean_dec_ref(v___f_668_);
v_a_833_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_729_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_729_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
else
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
lean_dec(v_a_726_);
lean_del_object(v___x_716_);
lean_dec(v_fst_713_);
lean_del_object(v___x_711_);
lean_dec(v_fst_709_);
lean_dec(v_a_705_);
lean_dec(v_a_703_);
lean_dec(v_a_701_);
lean_dec(v_a_684_);
lean_dec(v_head_669_);
lean_dec_ref(v___f_668_);
v_a_841_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v___x_727_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_727_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
lean_del_object(v___x_716_);
lean_dec(v_fst_713_);
lean_del_object(v___x_711_);
lean_dec(v_fst_709_);
lean_dec(v_a_705_);
lean_dec(v_a_703_);
lean_dec(v_a_701_);
lean_dec(v_a_684_);
lean_dec(v_head_669_);
lean_dec_ref(v___f_668_);
v_a_849_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_725_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_725_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
}
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
lean_dec(v_a_705_);
lean_dec(v_a_703_);
lean_dec(v_a_701_);
lean_dec(v_a_697_);
lean_dec(v_a_684_);
lean_dec(v_head_669_);
lean_dec_ref(v___f_668_);
v_a_860_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_706_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_706_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
lean_dec(v_a_703_);
lean_dec(v_a_701_);
lean_dec(v_a_697_);
lean_dec(v_a_684_);
lean_dec(v_head_669_);
lean_dec_ref(v___f_668_);
v_a_868_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_704_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_704_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec(v_a_701_);
lean_dec(v_a_697_);
lean_dec(v_a_684_);
lean_dec(v_head_669_);
lean_dec_ref(v___f_668_);
v_a_876_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_702_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_702_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
else
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
lean_dec(v_a_697_);
lean_dec(v_a_684_);
lean_dec(v_head_669_);
lean_dec_ref(v___f_668_);
v_a_884_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_700_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_700_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_dec(v_a_684_);
lean_dec(v_head_669_);
lean_dec_ref(v___f_668_);
v_a_892_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_696_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_696_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec(v_a_684_);
lean_dec(v_a_680_);
lean_dec(v_head_669_);
lean_dec_ref(v___f_668_);
lean_dec_ref(v___f_666_);
lean_dec(v___x_664_);
v_a_902_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_686_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_686_);
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
}
else
{
lean_dec(v_a_680_);
lean_dec(v_head_669_);
lean_dec_ref(v___f_668_);
lean_dec_ref(v___f_666_);
lean_dec_ref(v_alts_665_);
lean_dec(v___x_664_);
return v___x_683_;
}
}
else
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
lean_dec(v_head_669_);
lean_dec_ref(v___f_668_);
lean_dec_ref(v___f_666_);
lean_dec_ref(v_alts_665_);
lean_dec(v___x_664_);
v_a_910_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_679_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_679_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___boxed(lean_object* v_indVal_918_, lean_object* v___x_919_, lean_object* v_alts_920_, lean_object* v___f_921_, lean_object* v_numFields_922_, lean_object* v___f_923_, lean_object* v_head_924_, lean_object* v_xs_925_, lean_object* v_type_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2(v_indVal_918_, v___x_919_, v_alts_920_, v___f_921_, v_numFields_922_, v___f_923_, v_head_924_, v_xs_925_, v_type_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec_ref(v_xs_925_);
lean_dec(v_numFields_922_);
lean_dec_ref(v_indVal_918_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__1(lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_ref_942_; uint8_t v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v_ref_942_ = lean_ctor_get(v___y_939_, 2);
v___x_943_ = 0;
v___x_944_ = l_Lean_SourceInfo_fromRef(v_ref_942_, v___x_943_);
v___x_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__1___boxed(lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__1(v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__0(lean_object* v_rhs_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_962_, 0, v_rhs_954_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__0___boxed(lean_object* v_rhs_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__0(v_rhs_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
return v_res_971_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_instMonadEIO(lean_box(0));
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1(lean_object* v_msg_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v_toApplicative_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1080_; 
v___x_987_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__0);
v___x_988_ = l_StateRefT_x27_instMonad___redArg(v___x_987_);
v_toApplicative_989_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1080_ == 0)
{
lean_object* v_unused_1081_; 
v_unused_1081_ = lean_ctor_get(v___x_988_, 1);
lean_dec(v_unused_1081_);
v___x_991_ = v___x_988_;
v_isShared_992_ = v_isSharedCheck_1080_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_toApplicative_989_);
lean_dec(v___x_988_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1080_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v_toFunctor_993_; lean_object* v_toSeq_994_; lean_object* v_toSeqLeft_995_; lean_object* v_toSeqRight_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1078_; 
v_toFunctor_993_ = lean_ctor_get(v_toApplicative_989_, 0);
v_toSeq_994_ = lean_ctor_get(v_toApplicative_989_, 2);
v_toSeqLeft_995_ = lean_ctor_get(v_toApplicative_989_, 3);
v_toSeqRight_996_ = lean_ctor_get(v_toApplicative_989_, 4);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_toApplicative_989_);
if (v_isSharedCheck_1078_ == 0)
{
lean_object* v_unused_1079_; 
v_unused_1079_ = lean_ctor_get(v_toApplicative_989_, 1);
lean_dec(v_unused_1079_);
v___x_998_ = v_toApplicative_989_;
v_isShared_999_ = v_isSharedCheck_1078_;
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
v_isShared_999_ = v_isSharedCheck_1078_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___f_1000_; lean_object* v___f_1001_; lean_object* v___f_1002_; lean_object* v___f_1003_; lean_object* v___x_1004_; lean_object* v___f_1005_; lean_object* v___f_1006_; lean_object* v___f_1007_; lean_object* v___x_1009_; 
v___f_1000_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__1));
v___f_1001_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__2));
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
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1004_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v___f_1000_);
lean_ctor_set(v_reuseFailAlloc_1077_, 2, v___f_1007_);
lean_ctor_set(v_reuseFailAlloc_1077_, 3, v___f_1006_);
lean_ctor_set(v_reuseFailAlloc_1077_, 4, v___f_1005_);
v___x_1009_ = v_reuseFailAlloc_1077_;
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
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v___x_1009_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v___f_1001_);
v___x_1011_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
lean_object* v___x_1012_; lean_object* v_toApplicative_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1074_; 
v___x_1012_ = l_StateRefT_x27_instMonad___redArg(v___x_1011_);
v_toApplicative_1013_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1074_ == 0)
{
lean_object* v_unused_1075_; 
v_unused_1075_ = lean_ctor_get(v___x_1012_, 1);
lean_dec(v_unused_1075_);
v___x_1015_ = v___x_1012_;
v_isShared_1016_ = v_isSharedCheck_1074_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_toApplicative_1013_);
lean_dec(v___x_1012_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1074_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v_toFunctor_1017_; lean_object* v_toSeq_1018_; lean_object* v_toSeqLeft_1019_; lean_object* v_toSeqRight_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1072_; 
v_toFunctor_1017_ = lean_ctor_get(v_toApplicative_1013_, 0);
v_toSeq_1018_ = lean_ctor_get(v_toApplicative_1013_, 2);
v_toSeqLeft_1019_ = lean_ctor_get(v_toApplicative_1013_, 3);
v_toSeqRight_1020_ = lean_ctor_get(v_toApplicative_1013_, 4);
v_isSharedCheck_1072_ = !lean_is_exclusive(v_toApplicative_1013_);
if (v_isSharedCheck_1072_ == 0)
{
lean_object* v_unused_1073_; 
v_unused_1073_ = lean_ctor_get(v_toApplicative_1013_, 1);
lean_dec(v_unused_1073_);
v___x_1022_ = v_toApplicative_1013_;
v_isShared_1023_ = v_isSharedCheck_1072_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_toSeqRight_1020_);
lean_inc(v_toSeqLeft_1019_);
lean_inc(v_toSeq_1018_);
lean_inc(v_toFunctor_1017_);
lean_dec(v_toApplicative_1013_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1072_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___f_1024_; lean_object* v___f_1025_; lean_object* v___f_1026_; lean_object* v___f_1027_; lean_object* v___x_1028_; lean_object* v___f_1029_; lean_object* v___f_1030_; lean_object* v___f_1031_; lean_object* v___x_1033_; 
v___f_1024_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__3));
v___f_1025_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1017_);
v___f_1026_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1026_, 0, v_toFunctor_1017_);
v___f_1027_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1027_, 0, v_toFunctor_1017_);
v___x_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___f_1026_);
lean_ctor_set(v___x_1028_, 1, v___f_1027_);
v___f_1029_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1029_, 0, v_toSeqRight_1020_);
v___f_1030_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1030_, 0, v_toSeqLeft_1019_);
v___f_1031_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1031_, 0, v_toSeq_1018_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 4, v___f_1029_);
lean_ctor_set(v___x_1022_, 3, v___f_1030_);
lean_ctor_set(v___x_1022_, 2, v___f_1031_);
lean_ctor_set(v___x_1022_, 1, v___f_1024_);
lean_ctor_set(v___x_1022_, 0, v___x_1028_);
v___x_1033_ = v___x_1022_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1028_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v___f_1024_);
lean_ctor_set(v_reuseFailAlloc_1071_, 2, v___f_1031_);
lean_ctor_set(v_reuseFailAlloc_1071_, 3, v___f_1030_);
lean_ctor_set(v_reuseFailAlloc_1071_, 4, v___f_1029_);
v___x_1033_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
lean_object* v___x_1035_; 
if (v_isShared_1016_ == 0)
{
lean_ctor_set(v___x_1015_, 1, v___f_1025_);
lean_ctor_set(v___x_1015_, 0, v___x_1033_);
v___x_1035_ = v___x_1015_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1033_);
lean_ctor_set(v_reuseFailAlloc_1070_, 1, v___f_1025_);
v___x_1035_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
lean_object* v___x_1036_; lean_object* v_toApplicative_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1068_; 
v___x_1036_ = l_StateRefT_x27_instMonad___redArg(v___x_1035_);
v_toApplicative_1037_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1068_ == 0)
{
lean_object* v_unused_1069_; 
v_unused_1069_ = lean_ctor_get(v___x_1036_, 1);
lean_dec(v_unused_1069_);
v___x_1039_ = v___x_1036_;
v_isShared_1040_ = v_isSharedCheck_1068_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_toApplicative_1037_);
lean_dec(v___x_1036_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1068_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v_toFunctor_1041_; lean_object* v_toSeq_1042_; lean_object* v_toSeqLeft_1043_; lean_object* v_toSeqRight_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1066_; 
v_toFunctor_1041_ = lean_ctor_get(v_toApplicative_1037_, 0);
v_toSeq_1042_ = lean_ctor_get(v_toApplicative_1037_, 2);
v_toSeqLeft_1043_ = lean_ctor_get(v_toApplicative_1037_, 3);
v_toSeqRight_1044_ = lean_ctor_get(v_toApplicative_1037_, 4);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_toApplicative_1037_);
if (v_isSharedCheck_1066_ == 0)
{
lean_object* v_unused_1067_; 
v_unused_1067_ = lean_ctor_get(v_toApplicative_1037_, 1);
lean_dec(v_unused_1067_);
v___x_1046_ = v_toApplicative_1037_;
v_isShared_1047_ = v_isSharedCheck_1066_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_toSeqRight_1044_);
lean_inc(v_toSeqLeft_1043_);
lean_inc(v_toSeq_1042_);
lean_inc(v_toFunctor_1041_);
lean_dec(v_toApplicative_1037_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1066_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___f_1048_; lean_object* v___f_1049_; lean_object* v___f_1050_; lean_object* v___f_1051_; lean_object* v___x_1052_; lean_object* v___f_1053_; lean_object* v___f_1054_; lean_object* v___f_1055_; lean_object* v___x_1057_; 
v___f_1048_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__5));
v___f_1049_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___closed__6));
lean_inc_ref(v_toFunctor_1041_);
v___f_1050_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1050_, 0, v_toFunctor_1041_);
v___f_1051_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1051_, 0, v_toFunctor_1041_);
v___x_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___f_1050_);
lean_ctor_set(v___x_1052_, 1, v___f_1051_);
v___f_1053_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1053_, 0, v_toSeqRight_1044_);
v___f_1054_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1054_, 0, v_toSeqLeft_1043_);
v___f_1055_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1055_, 0, v_toSeq_1042_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 4, v___f_1053_);
lean_ctor_set(v___x_1046_, 3, v___f_1054_);
lean_ctor_set(v___x_1046_, 2, v___f_1055_);
lean_ctor_set(v___x_1046_, 1, v___f_1048_);
lean_ctor_set(v___x_1046_, 0, v___x_1052_);
v___x_1057_ = v___x_1046_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v___f_1048_);
lean_ctor_set(v_reuseFailAlloc_1065_, 2, v___f_1055_);
lean_ctor_set(v_reuseFailAlloc_1065_, 3, v___f_1054_);
lean_ctor_set(v_reuseFailAlloc_1065_, 4, v___f_1053_);
v___x_1057_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1059_; 
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 1, v___f_1049_);
lean_ctor_set(v___x_1039_, 0, v___x_1057_);
v___x_1059_ = v___x_1039_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1057_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v___f_1049_);
v___x_1059_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_46436__overap_1062_; lean_object* v___x_1063_; 
v___x_1060_ = lean_box(0);
v___x_1061_ = l_instInhabitedOfMonad___redArg(v___x_1059_, v___x_1060_);
v___x_46436__overap_1062_ = lean_panic_fn_borrowed(v___x_1061_, v_msg_979_);
lean_dec(v___x_1061_);
lean_inc(v___y_985_);
lean_inc_ref(v___y_984_);
lean_inc(v___y_983_);
lean_inc_ref(v___y_982_);
lean_inc(v___y_981_);
lean_inc_ref(v___y_980_);
v___x_1063_ = lean_apply_7(v___x_46436__overap_1062_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, lean_box(0));
return v___x_1063_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1___boxed(lean_object* v_msg_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1(v_msg_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(lean_object* v_msgData_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v___x_1097_; lean_object* v_env_1098_; lean_object* v___x_1099_; lean_object* v_toCold_1100_; lean_object* v_mctx_1101_; lean_object* v_lctx_1102_; lean_object* v_options_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1097_ = lean_st_ref_get(v___y_1095_);
v_env_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc_ref(v_env_1098_);
lean_dec(v___x_1097_);
v___x_1099_ = lean_st_ref_get(v___y_1093_);
v_toCold_1100_ = lean_ctor_get(v___y_1094_, 0);
v_mctx_1101_ = lean_ctor_get(v___x_1099_, 0);
lean_inc_ref(v_mctx_1101_);
lean_dec(v___x_1099_);
v_lctx_1102_ = lean_ctor_get(v___y_1092_, 2);
v_options_1103_ = lean_ctor_get(v_toCold_1100_, 2);
lean_inc_ref(v_options_1103_);
lean_inc_ref(v_lctx_1102_);
v___x_1104_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1104_, 0, v_env_1098_);
lean_ctor_set(v___x_1104_, 1, v_mctx_1101_);
lean_ctor_set(v___x_1104_, 2, v_lctx_1102_);
lean_ctor_set(v___x_1104_, 3, v_options_1103_);
v___x_1105_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
lean_ctor_set(v___x_1105_, 1, v_msgData_1091_);
v___x_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(v_msgData_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
return v_res_1113_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0(void){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = lean_box(1);
v___x_1115_ = l_Lean_MessageData_ofFormat(v___x_1114_);
return v___x_1115_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3(void){
_start:
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1119_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__2));
v___x_1120_ = l_Lean_MessageData_ofFormat(v___x_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12(lean_object* v_x_1121_, lean_object* v_x_1122_){
_start:
{
if (lean_obj_tag(v_x_1122_) == 0)
{
return v_x_1121_;
}
else
{
lean_object* v_head_1123_; lean_object* v_tail_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1146_; 
v_head_1123_ = lean_ctor_get(v_x_1122_, 0);
v_tail_1124_ = lean_ctor_get(v_x_1122_, 1);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_x_1122_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1126_ = v_x_1122_;
v_isShared_1127_ = v_isSharedCheck_1146_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_tail_1124_);
lean_inc(v_head_1123_);
lean_dec(v_x_1122_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1146_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v_before_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1144_; 
v_before_1128_ = lean_ctor_get(v_head_1123_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_head_1123_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; 
v_unused_1145_ = lean_ctor_get(v_head_1123_, 1);
lean_dec(v_unused_1145_);
v___x_1130_ = v_head_1123_;
v_isShared_1131_ = v_isSharedCheck_1144_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_before_1128_);
lean_dec(v_head_1123_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1144_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1132_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0);
if (v_isShared_1131_ == 0)
{
lean_ctor_set_tag(v___x_1130_, 7);
lean_ctor_set(v___x_1130_, 1, v___x_1132_);
lean_ctor_set(v___x_1130_, 0, v_x_1121_);
v___x_1134_ = v___x_1130_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_x_1121_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1135_; lean_object* v___x_1137_; 
v___x_1135_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3);
if (v_isShared_1127_ == 0)
{
lean_ctor_set_tag(v___x_1126_, 7);
lean_ctor_set(v___x_1126_, 1, v___x_1135_);
lean_ctor_set(v___x_1126_, 0, v___x_1134_);
v___x_1137_ = v___x_1126_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1134_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1138_ = l_Lean_MessageData_ofSyntax(v_before_1128_);
v___x_1139_ = l_Lean_indentD(v___x_1138_);
v___x_1140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1137_);
lean_ctor_set(v___x_1140_, 1, v___x_1139_);
v_x_1121_ = v___x_1140_;
v_x_1122_ = v_tail_1124_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(lean_object* v_opts_1147_, lean_object* v_opt_1148_){
_start:
{
lean_object* v_name_1149_; lean_object* v_defValue_1150_; lean_object* v_map_1151_; lean_object* v___x_1152_; 
v_name_1149_ = lean_ctor_get(v_opt_1148_, 0);
v_defValue_1150_ = lean_ctor_get(v_opt_1148_, 1);
v_map_1151_ = lean_ctor_get(v_opts_1147_, 0);
v___x_1152_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1151_, v_name_1149_);
if (lean_obj_tag(v___x_1152_) == 0)
{
uint8_t v___x_1153_; 
v___x_1153_ = lean_unbox(v_defValue_1150_);
return v___x_1153_;
}
else
{
lean_object* v_val_1154_; 
v_val_1154_ = lean_ctor_get(v___x_1152_, 0);
lean_inc(v_val_1154_);
lean_dec_ref_known(v___x_1152_, 1);
if (lean_obj_tag(v_val_1154_) == 1)
{
uint8_t v_v_1155_; 
v_v_1155_ = lean_ctor_get_uint8(v_val_1154_, 0);
lean_dec_ref_known(v_val_1154_, 0);
return v_v_1155_;
}
else
{
uint8_t v___x_1156_; 
lean_dec(v_val_1154_);
v___x_1156_ = lean_unbox(v_defValue_1150_);
return v___x_1156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___boxed(lean_object* v_opts_1157_, lean_object* v_opt_1158_){
_start:
{
uint8_t v_res_1159_; lean_object* v_r_1160_; 
v_res_1159_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(v_opts_1157_, v_opt_1158_);
lean_dec_ref(v_opt_1158_);
lean_dec_ref(v_opts_1157_);
v_r_1160_ = lean_box(v_res_1159_);
return v_r_1160_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1));
v___x_1165_ = l_Lean_MessageData_ofFormat(v___x_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(lean_object* v_msgData_1166_, lean_object* v_macroStack_1167_, lean_object* v___y_1168_){
_start:
{
lean_object* v_toCold_1170_; lean_object* v_options_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; 
v_toCold_1170_ = lean_ctor_get(v___y_1168_, 0);
v_options_1171_ = lean_ctor_get(v_toCold_1170_, 2);
v___x_1172_ = l_Lean_Elab_pp_macroStack;
v___x_1173_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(v_options_1171_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; 
lean_dec(v_macroStack_1167_);
v___x_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1174_, 0, v_msgData_1166_);
return v___x_1174_;
}
else
{
if (lean_obj_tag(v_macroStack_1167_) == 0)
{
lean_object* v___x_1175_; 
v___x_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1175_, 0, v_msgData_1166_);
return v___x_1175_;
}
else
{
lean_object* v_head_1176_; lean_object* v_after_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1192_; 
v_head_1176_ = lean_ctor_get(v_macroStack_1167_, 0);
lean_inc(v_head_1176_);
v_after_1177_ = lean_ctor_get(v_head_1176_, 1);
v_isSharedCheck_1192_ = !lean_is_exclusive(v_head_1176_);
if (v_isSharedCheck_1192_ == 0)
{
lean_object* v_unused_1193_; 
v_unused_1193_ = lean_ctor_get(v_head_1176_, 0);
lean_dec(v_unused_1193_);
v___x_1179_ = v_head_1176_;
v_isShared_1180_ = v_isSharedCheck_1192_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_after_1177_);
lean_dec(v_head_1176_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1192_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1181_; lean_object* v___x_1183_; 
v___x_1181_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0);
if (v_isShared_1180_ == 0)
{
lean_ctor_set_tag(v___x_1179_, 7);
lean_ctor_set(v___x_1179_, 1, v___x_1181_);
lean_ctor_set(v___x_1179_, 0, v_msgData_1166_);
v___x_1183_ = v___x_1179_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v_msgData_1166_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v_msgData_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1184_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_1185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1183_);
lean_ctor_set(v___x_1185_, 1, v___x_1184_);
v___x_1186_ = l_Lean_MessageData_ofSyntax(v_after_1177_);
v___x_1187_ = l_Lean_indentD(v___x_1186_);
v_msgData_1188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1188_, 0, v___x_1185_);
lean_ctor_set(v_msgData_1188_, 1, v___x_1187_);
v___x_1189_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12(v_msgData_1188_, v_macroStack_1167_);
v___x_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
return v___x_1190_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_msgData_1194_, lean_object* v_macroStack_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(v_msgData_1194_, v_macroStack_1195_, v___y_1196_);
lean_dec_ref(v___y_1196_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0___redArg(lean_object* v_msg_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_ref_1207_; lean_object* v___x_1208_; lean_object* v_a_1209_; lean_object* v_macroStack_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1221_; 
v_ref_1207_ = lean_ctor_get(v___y_1204_, 2);
v___x_1208_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(v_msg_1199_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
lean_inc(v_a_1209_);
lean_dec_ref(v___x_1208_);
v_macroStack_1210_ = lean_ctor_get(v___y_1200_, 1);
v___x_1211_ = l_Lean_Elab_getBetterRef(v_ref_1207_, v_macroStack_1210_);
lean_inc(v_macroStack_1210_);
v___x_1212_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(v_a_1209_, v_macroStack_1210_, v___y_1204_);
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1215_ = v___x_1212_;
v_isShared_1216_ = v_isSharedCheck_1221_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1212_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1221_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1211_);
lean_ctor_set(v___x_1217_, 1, v_a_1213_);
if (v_isShared_1216_ == 0)
{
lean_ctor_set_tag(v___x_1215_, 1);
lean_ctor_set(v___x_1215_, 0, v___x_1217_);
v___x_1219_ = v___x_1215_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1217_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0___redArg(v_msg_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
return v_res_1230_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__0));
v___x_1233_ = l_Lean_stringToMessageData(v___x_1232_);
return v___x_1233_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__2));
v___x_1236_ = l_Lean_stringToMessageData(v___x_1235_);
return v___x_1236_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__7(void){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1240_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__6));
v___x_1241_ = lean_unsigned_to_nat(11u);
v___x_1242_ = lean_unsigned_to_nat(122u);
v___x_1243_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__5));
v___x_1244_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__4));
v___x_1245_ = l_mkPanicMessageWithDecl(v___x_1244_, v___x_1243_, v___x_1242_, v___x_1241_, v___x_1240_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0(lean_object* v_constName_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v___x_1262_; lean_object* v_env_1263_; uint8_t v___x_1264_; lean_object* v___x_1265_; 
v___x_1262_ = lean_st_ref_get(v___y_1252_);
v_env_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc_ref(v_env_1263_);
lean_dec(v___x_1262_);
v___x_1264_ = 0;
lean_inc(v_constName_1246_);
v___x_1265_ = l_Lean_Environment_findAsync_x3f(v_env_1263_, v_constName_1246_, v___x_1264_);
if (lean_obj_tag(v___x_1265_) == 1)
{
lean_object* v_val_1266_; uint8_t v_kind_1267_; 
v_val_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_val_1266_);
lean_dec_ref_known(v___x_1265_, 1);
v_kind_1267_ = lean_ctor_get_uint8(v_val_1266_, sizeof(void*)*3);
if (v_kind_1267_ == 6)
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1266_);
if (lean_obj_tag(v___x_1268_) == 6)
{
lean_object* v_val_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_dec(v_constName_1246_);
v_val_1269_ = lean_ctor_get(v___x_1268_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1268_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_val_1269_);
lean_dec(v___x_1268_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
lean_ctor_set_tag(v___x_1271_, 0);
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_val_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
lean_dec_ref(v___x_1268_);
v___x_1277_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__7);
v___x_1278_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1(v___x_1277_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1287_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1281_ = v___x_1278_;
v_isShared_1282_ = v_isSharedCheck_1287_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1278_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1287_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
if (lean_obj_tag(v_a_1279_) == 0)
{
lean_del_object(v___x_1281_);
goto v___jp_1254_;
}
else
{
lean_object* v_val_1283_; lean_object* v___x_1285_; 
lean_dec(v_constName_1246_);
v_val_1283_ = lean_ctor_get(v_a_1279_, 0);
lean_inc(v_val_1283_);
lean_dec_ref_known(v_a_1279_, 1);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v_val_1283_);
v___x_1285_ = v___x_1281_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_val_1283_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec(v_constName_1246_);
v_a_1288_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1278_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1278_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
else
{
lean_dec(v_val_1266_);
goto v___jp_1254_;
}
}
else
{
lean_dec(v___x_1265_);
goto v___jp_1254_;
}
v___jp_1254_:
{
lean_object* v___x_1255_; uint8_t v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1255_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1);
v___x_1256_ = 0;
v___x_1257_ = l_Lean_MessageData_ofConstName(v_constName_1246_, v___x_1256_);
v___x_1258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1255_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
v___x_1259_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__3);
v___x_1260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1258_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
v___x_1261_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0___redArg(v___x_1260_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
return v___x_1261_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___boxed(lean_object* v_constName_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0(v_constName_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__6(size_t v_sz_1305_, size_t v_i_1306_, lean_object* v_bs_1307_){
_start:
{
uint8_t v___x_1308_; 
v___x_1308_ = lean_usize_dec_lt(v_i_1306_, v_sz_1305_);
if (v___x_1308_ == 0)
{
return v_bs_1307_;
}
else
{
lean_object* v_v_1309_; lean_object* v___x_1310_; lean_object* v_bs_x27_1311_; size_t v___x_1312_; size_t v___x_1313_; lean_object* v___x_1314_; 
v_v_1309_ = lean_array_uget(v_bs_1307_, v_i_1306_);
v___x_1310_ = lean_unsigned_to_nat(0u);
v_bs_x27_1311_ = lean_array_uset(v_bs_1307_, v_i_1306_, v___x_1310_);
v___x_1312_ = ((size_t)1ULL);
v___x_1313_ = lean_usize_add(v_i_1306_, v___x_1312_);
v___x_1314_ = lean_array_uset(v_bs_x27_1311_, v_i_1306_, v_v_1309_);
v_i_1306_ = v___x_1313_;
v_bs_1307_ = v___x_1314_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__6___boxed(lean_object* v_sz_1316_, lean_object* v_i_1317_, lean_object* v_bs_1318_){
_start:
{
size_t v_sz_boxed_1319_; size_t v_i_boxed_1320_; lean_object* v_res_1321_; 
v_sz_boxed_1319_ = lean_unbox_usize(v_sz_1316_);
lean_dec(v_sz_1316_);
v_i_boxed_1320_ = lean_unbox_usize(v_i_1317_);
lean_dec(v_i_1317_);
v_res_1321_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__6(v_sz_boxed_1319_, v_i_boxed_1320_, v_bs_1318_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg(lean_object* v_indVal_1326_, lean_object* v_as_x27_1327_, lean_object* v_b_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
if (lean_obj_tag(v_as_x27_1327_) == 0)
{
lean_object* v___x_1336_; 
lean_dec_ref(v_indVal_1326_);
v___x_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1336_, 0, v_b_1328_);
return v___x_1336_;
}
else
{
lean_object* v_head_1337_; lean_object* v_tail_1338_; lean_object* v___x_1339_; 
v_head_1337_ = lean_ctor_get(v_as_x27_1327_, 0);
v_tail_1338_ = lean_ctor_get(v_as_x27_1327_, 1);
lean_inc(v_head_1337_);
v___x_1339_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0(v_head_1337_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v_toConstantVal_1341_; lean_object* v_numFields_1342_; lean_object* v_type_1343_; lean_object* v___f_1344_; lean_object* v___f_1345_; lean_object* v___x_1346_; lean_object* v_alts_1347_; lean_object* v___f_1348_; uint8_t v___x_1349_; lean_object* v___x_1350_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1340_);
lean_dec_ref_known(v___x_1339_, 1);
v_toConstantVal_1341_ = lean_ctor_get(v_a_1340_, 0);
lean_inc_ref(v_toConstantVal_1341_);
v_numFields_1342_ = lean_ctor_get(v_a_1340_, 4);
lean_inc(v_numFields_1342_);
lean_dec(v_a_1340_);
v_type_1343_ = lean_ctor_get(v_toConstantVal_1341_, 2);
lean_inc_ref(v_type_1343_);
lean_dec_ref(v_toConstantVal_1341_);
v___f_1344_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__0));
v___f_1345_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__1));
v___x_1346_ = lean_unsigned_to_nat(0u);
v_alts_1347_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__2));
lean_inc(v_head_1337_);
lean_inc_ref(v_indVal_1326_);
v___f_1348_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___boxed), 16, 7);
lean_closure_set(v___f_1348_, 0, v_indVal_1326_);
lean_closure_set(v___f_1348_, 1, v___x_1346_);
lean_closure_set(v___f_1348_, 2, v_alts_1347_);
lean_closure_set(v___f_1348_, 3, v___f_1344_);
lean_closure_set(v___f_1348_, 4, v_numFields_1342_);
lean_closure_set(v___f_1348_, 5, v___f_1345_);
lean_closure_set(v___f_1348_, 6, v_head_1337_);
v___x_1349_ = 0;
v___x_1350_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg(v_type_1343_, v___f_1348_, v___x_1349_, v___x_1349_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; size_t v_sz_1352_; size_t v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_a_1351_);
lean_dec_ref_known(v___x_1350_, 1);
v_sz_1352_ = lean_array_size(v_a_1351_);
v___x_1353_ = ((size_t)0ULL);
v___x_1354_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__6(v_sz_1352_, v___x_1353_, v_a_1351_);
v___x_1355_ = l_Array_append___redArg(v_b_1328_, v___x_1354_);
lean_dec_ref(v___x_1354_);
v_as_x27_1327_ = v_tail_1338_;
v_b_1328_ = v___x_1355_;
goto _start;
}
else
{
lean_dec_ref(v_b_1328_);
lean_dec_ref(v_indVal_1326_);
return v___x_1350_;
}
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_dec_ref(v_b_1328_);
lean_dec_ref(v_indVal_1326_);
v_a_1357_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1339_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1339_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___boxed(lean_object* v_indVal_1365_, lean_object* v_as_x27_1366_, lean_object* v_b_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg(v_indVal_1365_, v_as_x27_1366_, v_b_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v_as_x27_1366_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts(lean_object* v_indVal_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v_ctors_1384_; lean_object* v_alts_1385_; lean_object* v___x_1386_; 
v_ctors_1384_ = lean_ctor_get(v_indVal_1376_, 4);
lean_inc(v_ctors_1384_);
v_alts_1385_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__2));
v___x_1386_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg(v_indVal_1376_, v_ctors_1384_, v_alts_1385_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
lean_dec(v_ctors_1384_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1396_; 
v_a_1387_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1389_ = v___x_1386_;
v_isShared_1390_ = v_isSharedCheck_1396_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1386_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1396_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1394_; 
v___x_1391_ = lean_array_pop(v_a_1387_);
v___x_1392_ = lean_array_pop(v___x_1391_);
if (v_isShared_1390_ == 0)
{
lean_ctor_set(v___x_1389_, 0, v___x_1392_);
v___x_1394_ = v___x_1389_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v___x_1392_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
else
{
return v___x_1386_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts___boxed(lean_object* v_indVal_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts(v_indVal_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_);
lean_dec(v_a_1403_);
lean_dec_ref(v_a_1402_);
lean_dec(v_a_1401_);
lean_dec_ref(v_a_1400_);
lean_dec(v_a_1399_);
lean_dec_ref(v_a_1398_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2(lean_object* v_upperBound_1406_, lean_object* v___x_1407_, lean_object* v_xs_1408_, lean_object* v_a_1409_, lean_object* v_inst_1410_, lean_object* v_R_1411_, lean_object* v_a_1412_, lean_object* v_b_1413_, lean_object* v_c_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg(v_upperBound_1406_, v___x_1407_, v_xs_1408_, v_a_1409_, v_a_1412_, v_b_1413_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___boxed(lean_object* v_upperBound_1423_, lean_object* v___x_1424_, lean_object* v_xs_1425_, lean_object* v_a_1426_, lean_object* v_inst_1427_, lean_object* v_R_1428_, lean_object* v_a_1429_, lean_object* v_b_1430_, lean_object* v_c_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2(v_upperBound_1423_, v___x_1424_, v_xs_1425_, v_a_1426_, v_inst_1427_, v_R_1428_, v_a_1429_, v_b_1430_, v_c_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec_ref(v_a_1426_);
lean_dec_ref(v_xs_1425_);
lean_dec(v___x_1424_);
lean_dec(v_upperBound_1423_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3(lean_object* v_upperBound_1440_, lean_object* v_inst_1441_, lean_object* v_R_1442_, lean_object* v_a_1443_, lean_object* v_b_1444_, lean_object* v_c_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3___redArg(v_upperBound_1440_, v_a_1443_, v_b_1444_, v___y_1450_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3___boxed(lean_object* v_upperBound_1454_, lean_object* v_inst_1455_, lean_object* v_R_1456_, lean_object* v_a_1457_, lean_object* v_b_1458_, lean_object* v_c_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3(v_upperBound_1454_, v_inst_1455_, v_R_1456_, v_a_1457_, v_b_1458_, v_c_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v_upperBound_1454_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4(lean_object* v_upperBound_1468_, lean_object* v_inst_1469_, lean_object* v_R_1470_, lean_object* v_a_1471_, lean_object* v_b_1472_, lean_object* v_c_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4___redArg(v_upperBound_1468_, v_a_1471_, v_b_1472_, v___y_1478_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4___boxed(lean_object* v_upperBound_1482_, lean_object* v_inst_1483_, lean_object* v_R_1484_, lean_object* v_a_1485_, lean_object* v_b_1486_, lean_object* v_c_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4(v_upperBound_1482_, v_inst_1483_, v_R_1484_, v_a_1485_, v_b_1486_, v_c_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v_upperBound_1482_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7(lean_object* v_indVal_1496_, lean_object* v_as_1497_, lean_object* v_as_x27_1498_, lean_object* v_b_1499_, lean_object* v_a_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg(v_indVal_1496_, v_as_x27_1498_, v_b_1499_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___boxed(lean_object* v_indVal_1509_, lean_object* v_as_1510_, lean_object* v_as_x27_1511_, lean_object* v_b_1512_, lean_object* v_a_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7(v_indVal_1509_, v_as_1510_, v_as_x27_1511_, v_b_1512_, v_a_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v_as_x27_1511_);
lean_dec(v_as_1510_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0(lean_object* v_00_u03b1_1522_, lean_object* v_msg_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0___redArg(v_msg_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1532_, lean_object* v_msg_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0(v_00_u03b1_1532_, v_msg_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3(lean_object* v_msgData_1542_, lean_object* v_macroStack_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(v_msgData_1542_, v_macroStack_1543_, v___y_1548_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___boxed(lean_object* v_msgData_1552_, lean_object* v_macroStack_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3(v_msgData_1552_, v_macroStack_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld(lean_object* v_header_1575_, lean_object* v_indVal_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v___x_1584_; 
lean_inc_ref(v_indVal_1576_);
v___x_1584_ = l_Lean_Elab_Deriving_mkDiscrs(v_header_1575_, v_indVal_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1586_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v___x_1584_, 1);
v___x_1586_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts(v_indVal_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1617_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1589_ = v___x_1586_;
v_isShared_1590_ = v_isSharedCheck_1617_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1586_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1617_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v_ref_1591_; uint8_t v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; size_t v_sz_1600_; size_t v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1615_; 
v_ref_1591_ = lean_ctor_get(v_a_1581_, 2);
v___x_1592_ = 0;
v___x_1593_ = l_Lean_SourceInfo_fromRef(v_ref_1591_, v___x_1592_);
v___x_1594_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__0));
v___x_1595_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__1));
lean_inc_n(v___x_1593_, 6);
v___x_1596_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1593_);
lean_ctor_set(v___x_1596_, 1, v___x_1594_);
v___x_1597_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_1598_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11);
v___x_1599_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1593_);
lean_ctor_set(v___x_1599_, 1, v___x_1597_);
lean_ctor_set(v___x_1599_, 2, v___x_1598_);
v_sz_1600_ = lean_array_size(v_a_1585_);
v___x_1601_ = ((size_t)0ULL);
v___x_1602_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__1(v_sz_1600_, v___x_1601_, v_a_1585_);
v___x_1603_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__14, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__14_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__14);
v___x_1604_ = l_Lean_mkSepArray(v___x_1602_, v___x_1603_);
lean_dec_ref(v___x_1602_);
v___x_1605_ = l_Array_append___redArg(v___x_1598_, v___x_1604_);
lean_dec_ref(v___x_1604_);
v___x_1606_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1593_);
lean_ctor_set(v___x_1606_, 1, v___x_1597_);
lean_ctor_set(v___x_1606_, 2, v___x_1605_);
v___x_1607_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__2));
v___x_1608_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1593_);
lean_ctor_set(v___x_1608_, 1, v___x_1607_);
v___x_1609_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__4));
v___x_1610_ = l_Array_append___redArg(v___x_1598_, v_a_1587_);
lean_dec(v_a_1587_);
v___x_1611_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1593_);
lean_ctor_set(v___x_1611_, 1, v___x_1597_);
lean_ctor_set(v___x_1611_, 2, v___x_1610_);
v___x_1612_ = l_Lean_Syntax_node1(v___x_1593_, v___x_1609_, v___x_1611_);
lean_inc_ref(v___x_1599_);
v___x_1613_ = l_Lean_Syntax_node6(v___x_1593_, v___x_1595_, v___x_1596_, v___x_1599_, v___x_1599_, v___x_1606_, v___x_1608_, v___x_1612_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 0, v___x_1613_);
v___x_1615_ = v___x_1589_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v___x_1613_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
else
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
lean_dec(v_a_1585_);
v_a_1618_ = lean_ctor_get(v___x_1586_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___x_1586_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1586_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1618_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
else
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
lean_dec_ref(v_indVal_1576_);
v_a_1626_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v___x_1584_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1584_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___boxed(lean_object* v_header_1634_, lean_object* v_indVal_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld(v_header_1634_, v_indVal_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_);
lean_dec(v_a_1641_);
lean_dec_ref(v_a_1640_);
lean_dec(v_a_1639_);
lean_dec_ref(v_a_1638_);
lean_dec(v_a_1637_);
lean_dec_ref(v_a_1636_);
return v_res_1643_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1(lean_object* v_msg_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_24886__overap_1654_; lean_object* v___x_1655_; 
v___x_1653_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___closed__0, &l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___closed__0);
v___x_24886__overap_1654_ = lean_panic_fn_borrowed(v___x_1653_, v_msg_1645_);
lean_inc(v___y_1651_);
lean_inc_ref(v___y_1650_);
lean_inc(v___y_1649_);
lean_inc_ref(v___y_1648_);
lean_inc(v___y_1647_);
lean_inc_ref(v___y_1646_);
v___x_1655_ = lean_apply_7(v___x_24886__overap_1654_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, lean_box(0));
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___boxed(lean_object* v_msg_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1(v_msg_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg___lam__0(uint8_t v_a_1665_, lean_object* v___x_1666_, lean_object* v___x_1667_, lean_object* v_snd_1668_, lean_object* v_rhs_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v_toCold_1677_; lean_object* v_ref_1678_; lean_object* v_quotContext_1679_; lean_object* v_currMacroScope_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v_toCold_1677_ = lean_ctor_get(v___y_1674_, 0);
v_ref_1678_ = lean_ctor_get(v___y_1674_, 2);
v_quotContext_1679_ = lean_ctor_get(v_toCold_1677_, 8);
v_currMacroScope_1680_ = lean_ctor_get(v_toCold_1677_, 9);
v___x_1681_ = l_Lean_SourceInfo_fromRef(v_ref_1678_, v_a_1665_);
v___x_1682_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3));
v___x_1683_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__5);
v___x_1684_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__8));
lean_inc_n(v_currMacroScope_1680_, 3);
lean_inc_n(v_quotContext_1679_, 3);
v___x_1685_ = l_Lean_addMacroScope(v_quotContext_1679_, v___x_1684_, v_currMacroScope_1680_);
v___x_1686_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__12));
lean_inc_n(v___x_1681_, 11);
v___x_1687_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1681_);
lean_ctor_set(v___x_1687_, 1, v___x_1683_);
lean_ctor_set(v___x_1687_, 2, v___x_1685_);
lean_ctor_set(v___x_1687_, 3, v___x_1686_);
v___x_1688_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_1689_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__16));
v___x_1690_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18));
v___x_1691_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__19));
v___x_1692_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1681_);
lean_ctor_set(v___x_1692_, 1, v___x_1691_);
v___x_1693_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__21));
v___x_1694_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23);
v___x_1695_ = lean_box(0);
v___x_1696_ = l_Lean_addMacroScope(v_quotContext_1679_, v___x_1695_, v_currMacroScope_1680_);
v___x_1697_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__33));
v___x_1698_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1681_);
lean_ctor_set(v___x_1698_, 1, v___x_1694_);
lean_ctor_set(v___x_1698_, 2, v___x_1696_);
lean_ctor_set(v___x_1698_, 3, v___x_1697_);
v___x_1699_ = l_Lean_Syntax_node1(v___x_1681_, v___x_1693_, v___x_1698_);
v___x_1700_ = l_Lean_Syntax_node2(v___x_1681_, v___x_1690_, v___x_1692_, v___x_1699_);
v___x_1701_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35);
v___x_1702_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__36));
v___x_1703_ = l_Lean_addMacroScope(v_quotContext_1679_, v___x_1702_, v_currMacroScope_1680_);
v___x_1704_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__39));
v___x_1705_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1681_);
lean_ctor_set(v___x_1705_, 1, v___x_1701_);
lean_ctor_set(v___x_1705_, 2, v___x_1703_);
lean_ctor_set(v___x_1705_, 3, v___x_1704_);
v___x_1706_ = l_Lean_Syntax_node2(v___x_1681_, v___x_1688_, v___x_1666_, v___x_1667_);
v___x_1707_ = l_Lean_Syntax_node2(v___x_1681_, v___x_1682_, v___x_1705_, v___x_1706_);
v___x_1708_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__40));
v___x_1709_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1681_);
lean_ctor_set(v___x_1709_, 1, v___x_1708_);
v___x_1710_ = l_Lean_Syntax_node3(v___x_1681_, v___x_1689_, v___x_1700_, v___x_1707_, v___x_1709_);
v___x_1711_ = l_Lean_Syntax_node2(v___x_1681_, v___x_1688_, v___x_1710_, v_rhs_1669_);
v___x_1712_ = l_Lean_Syntax_node2(v___x_1681_, v___x_1682_, v___x_1687_, v___x_1711_);
lean_inc(v___y_1675_);
lean_inc_ref(v___y_1674_);
lean_inc(v___y_1673_);
lean_inc_ref(v___y_1672_);
lean_inc(v___y_1671_);
lean_inc_ref(v___y_1670_);
v___x_1713_ = lean_apply_8(v_snd_1668_, v___x_1712_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, lean_box(0));
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg___lam__0___boxed(lean_object* v_a_1714_, lean_object* v___x_1715_, lean_object* v___x_1716_, lean_object* v_snd_1717_, lean_object* v_rhs_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
uint8_t v_a_26161__boxed_1726_; lean_object* v_res_1727_; 
v_a_26161__boxed_1726_ = lean_unbox(v_a_1714_);
v_res_1727_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg___lam__0(v_a_26161__boxed_1726_, v___x_1715_, v___x_1716_, v_snd_1717_, v_rhs_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg(lean_object* v_upperBound_1729_, lean_object* v_indVal_1730_, lean_object* v_xs_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_, lean_object* v_b_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v_a_1741_; uint8_t v___x_1745_; 
v___x_1745_ = lean_nat_dec_lt(v_a_1733_, v_upperBound_1729_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; 
lean_dec(v_a_1733_);
v___x_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1746_, 0, v_b_1734_);
return v___x_1746_;
}
else
{
lean_object* v_snd_1747_; lean_object* v_fst_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1849_; 
v_snd_1747_ = lean_ctor_get(v_b_1734_, 1);
v_fst_1748_ = lean_ctor_get(v_b_1734_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v_b_1734_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1750_ = v_b_1734_;
v_isShared_1751_ = v_isSharedCheck_1849_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_snd_1747_);
lean_inc(v_fst_1748_);
lean_dec(v_b_1734_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1849_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v_fst_1752_; lean_object* v_snd_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1848_; 
v_fst_1752_ = lean_ctor_get(v_snd_1747_, 0);
v_snd_1753_ = lean_ctor_get(v_snd_1747_, 1);
v_isSharedCheck_1848_ = !lean_is_exclusive(v_snd_1747_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1755_ = v_snd_1747_;
v_isShared_1756_ = v_isSharedCheck_1848_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_snd_1753_);
lean_inc(v_fst_1752_);
lean_dec(v_snd_1747_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1848_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v_numParams_1757_; lean_object* v_lctx_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; uint8_t v___x_1762_; 
v_numParams_1757_ = lean_ctor_get(v_indVal_1730_, 1);
v_lctx_1758_ = lean_ctor_get(v___y_1735_, 2);
v___x_1759_ = l_Lean_instInhabitedExpr;
v___x_1760_ = lean_nat_add(v_numParams_1757_, v_a_1733_);
v___x_1761_ = lean_array_get_borrowed(v___x_1759_, v_xs_1731_, v___x_1760_);
lean_dec(v___x_1760_);
lean_inc(v___x_1761_);
lean_inc_ref(v_lctx_1758_);
v___x_1762_ = l_Lean_Meta_occursOrInType(v_lctx_1758_, v___x_1761_, v_a_1732_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1763_ = l_Lean_Expr_fvarId_x21(v___x_1761_);
v___x_1764_ = l_Lean_FVarId_getUserName___redArg(v___x_1763_, v___y_1735_, v___y_1737_, v___y_1738_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1766_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc_n(v_a_1765_, 2);
lean_dec_ref_known(v___x_1764_, 1);
v___x_1766_ = l_Lean_Core_mkFreshUserName(v_a_1765_, v___y_1737_, v___y_1738_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref_known(v___x_1766_, 1);
v___x_1768_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg___closed__0));
v___x_1769_ = lean_name_append_after(v_a_1765_, v___x_1768_);
v___x_1770_ = l_Lean_Core_mkFreshUserName(v___x_1769_, v___y_1737_, v___y_1738_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1772_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref_known(v___x_1770_, 1);
lean_inc(v___y_1738_);
lean_inc_ref(v___y_1737_);
lean_inc(v___y_1736_);
lean_inc_ref(v___y_1735_);
lean_inc(v___x_1761_);
v___x_1772_ = lean_infer_type(v___x_1761_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v___x_1774_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1773_);
lean_dec_ref_known(v___x_1772_, 1);
v___x_1774_ = l_Lean_Meta_isProp(v_a_1773_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; uint8_t v___x_1780_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_a_1775_);
lean_dec_ref_known(v___x_1774_, 1);
v___x_1776_ = l_Lean_mkIdent(v_a_1767_);
v___x_1777_ = l_Lean_mkIdent(v_a_1771_);
lean_inc(v___x_1776_);
v___x_1778_ = lean_array_push(v_fst_1748_, v___x_1776_);
lean_inc(v___x_1777_);
v___x_1779_ = lean_array_push(v_fst_1752_, v___x_1777_);
v___x_1780_ = lean_unbox(v_a_1775_);
if (v___x_1780_ == 0)
{
lean_object* v___f_1781_; lean_object* v___x_1783_; 
v___f_1781_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_1781_, 0, v_a_1775_);
lean_closure_set(v___f_1781_, 1, v___x_1776_);
lean_closure_set(v___f_1781_, 2, v___x_1777_);
lean_closure_set(v___f_1781_, 3, v_snd_1753_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 1, v___f_1781_);
lean_ctor_set(v___x_1755_, 0, v___x_1779_);
v___x_1783_ = v___x_1755_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1779_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v___f_1781_);
v___x_1783_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
lean_object* v___x_1785_; 
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 1, v___x_1783_);
lean_ctor_set(v___x_1750_, 0, v___x_1778_);
v___x_1785_ = v___x_1750_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1778_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v___x_1783_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
v_a_1741_ = v___x_1785_;
goto v___jp_1740_;
}
}
}
else
{
lean_object* v___x_1789_; 
lean_dec(v___x_1777_);
lean_dec(v___x_1776_);
lean_dec(v_a_1775_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v___x_1779_);
v___x_1789_ = v___x_1755_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1779_);
lean_ctor_set(v_reuseFailAlloc_1793_, 1, v_snd_1753_);
v___x_1789_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
lean_object* v___x_1791_; 
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 1, v___x_1789_);
lean_ctor_set(v___x_1750_, 0, v___x_1778_);
v___x_1791_ = v___x_1750_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v___x_1778_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v___x_1789_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
v_a_1741_ = v___x_1791_;
goto v___jp_1740_;
}
}
}
}
else
{
lean_object* v_a_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1801_; 
lean_dec(v_a_1771_);
lean_dec(v_a_1767_);
lean_del_object(v___x_1755_);
lean_dec(v_snd_1753_);
lean_dec(v_fst_1752_);
lean_del_object(v___x_1750_);
lean_dec(v_fst_1748_);
lean_dec(v_a_1733_);
v_a_1794_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1801_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1801_ == 0)
{
v___x_1796_ = v___x_1774_;
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_a_1794_);
lean_dec(v___x_1774_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1801_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
else
{
lean_object* v_a_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1809_; 
lean_dec(v_a_1771_);
lean_dec(v_a_1767_);
lean_del_object(v___x_1755_);
lean_dec(v_snd_1753_);
lean_dec(v_fst_1752_);
lean_del_object(v___x_1750_);
lean_dec(v_fst_1748_);
lean_dec(v_a_1733_);
v_a_1802_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1804_ = v___x_1772_;
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_a_1802_);
lean_dec(v___x_1772_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1809_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1807_; 
if (v_isShared_1805_ == 0)
{
v___x_1807_ = v___x_1804_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
else
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1817_; 
lean_dec(v_a_1767_);
lean_del_object(v___x_1755_);
lean_dec(v_snd_1753_);
lean_dec(v_fst_1752_);
lean_del_object(v___x_1750_);
lean_dec(v_fst_1748_);
lean_dec(v_a_1733_);
v_a_1810_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1812_ = v___x_1770_;
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1770_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1815_; 
if (v_isShared_1813_ == 0)
{
v___x_1815_ = v___x_1812_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_a_1810_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
}
else
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
lean_dec(v_a_1765_);
lean_del_object(v___x_1755_);
lean_dec(v_snd_1753_);
lean_dec(v_fst_1752_);
lean_del_object(v___x_1750_);
lean_dec(v_fst_1748_);
lean_dec(v_a_1733_);
v_a_1818_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v___x_1766_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1766_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1823_; 
if (v_isShared_1821_ == 0)
{
v___x_1823_ = v___x_1820_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_a_1818_);
v___x_1823_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
return v___x_1823_;
}
}
}
}
else
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1833_; 
lean_del_object(v___x_1755_);
lean_dec(v_snd_1753_);
lean_dec(v_fst_1752_);
lean_del_object(v___x_1750_);
lean_dec(v_fst_1748_);
lean_dec(v_a_1733_);
v_a_1826_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1828_ = v___x_1764_;
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1764_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1833_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_a_1826_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
}
}
}
}
else
{
lean_object* v_ref_1834_; uint8_t v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1843_; 
v_ref_1834_ = lean_ctor_get(v___y_1737_, 2);
v___x_1835_ = 0;
v___x_1836_ = l_Lean_SourceInfo_fromRef(v_ref_1834_, v___x_1835_);
v___x_1837_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8));
v___x_1838_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__9));
lean_inc(v___x_1836_);
v___x_1839_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1836_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
v___x_1840_ = l_Lean_Syntax_node1(v___x_1836_, v___x_1837_, v___x_1839_);
v___x_1841_ = lean_array_push(v_fst_1748_, v___x_1840_);
if (v_isShared_1756_ == 0)
{
v___x_1843_ = v___x_1755_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_fst_1752_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v_snd_1753_);
v___x_1843_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
lean_object* v___x_1845_; 
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 1, v___x_1843_);
lean_ctor_set(v___x_1750_, 0, v___x_1841_);
v___x_1845_ = v___x_1750_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1841_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
v_a_1741_ = v___x_1845_;
goto v___jp_1740_;
}
}
}
}
}
}
v___jp_1740_:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = lean_unsigned_to_nat(1u);
v___x_1743_ = lean_nat_add(v_a_1733_, v___x_1742_);
lean_dec(v_a_1733_);
v_a_1733_ = v___x_1743_;
v_b_1734_ = v_a_1741_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg___boxed(lean_object* v_upperBound_1850_, lean_object* v_indVal_1851_, lean_object* v_xs_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_b_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg(v_upperBound_1850_, v_indVal_1851_, v_xs_1852_, v_a_1853_, v_a_1854_, v_b_1855_, v___y_1856_, v___y_1857_, v___y_1858_, v___y_1859_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec_ref(v_a_1853_);
lean_dec_ref(v_xs_1852_);
lean_dec_ref(v_indVal_1851_);
lean_dec(v_upperBound_1850_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2(lean_object* v___f_1880_, lean_object* v_numFields_1881_, lean_object* v_indVal_1882_, lean_object* v___f_1883_, lean_object* v_xs_1884_, lean_object* v_type_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Lean_Core_betaReduce(v_type_1885_, v___y_1890_, v___y_1891_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
lean_inc(v_a_1894_);
lean_dec_ref_known(v___x_1893_, 1);
v___x_1895_ = lean_unsigned_to_nat(0u);
v___x_1896_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__2));
v___x_1897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
lean_ctor_set(v___x_1897_, 1, v___f_1880_);
v___x_1898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1896_);
lean_ctor_set(v___x_1898_, 1, v___x_1897_);
v___x_1899_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg(v_numFields_1881_, v_indVal_1882_, v_xs_1884_, v_a_1894_, v___x_1895_, v___x_1898_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
lean_dec(v_a_1894_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; lean_object* v_snd_1901_; lean_object* v_toCold_1902_; lean_object* v_fst_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_2003_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc(v_a_1900_);
lean_dec_ref_known(v___x_1899_, 1);
v_snd_1901_ = lean_ctor_get(v_a_1900_, 1);
lean_inc(v_snd_1901_);
v_toCold_1902_ = lean_ctor_get(v___y_1890_, 0);
v_fst_1903_ = lean_ctor_get(v_a_1900_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_a_1900_);
if (v_isSharedCheck_2003_ == 0)
{
lean_object* v_unused_2004_; 
v_unused_2004_ = lean_ctor_get(v_a_1900_, 1);
lean_dec(v_unused_2004_);
v___x_1905_ = v_a_1900_;
v_isShared_1906_ = v_isSharedCheck_2003_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_fst_1903_);
lean_dec(v_a_1900_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_2003_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v_fst_1907_; lean_object* v_snd_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_2002_; 
v_fst_1907_ = lean_ctor_get(v_snd_1901_, 0);
v_snd_1908_ = lean_ctor_get(v_snd_1901_, 1);
v_isSharedCheck_2002_ = !lean_is_exclusive(v_snd_1901_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1910_ = v_snd_1901_;
v_isShared_1911_ = v_isSharedCheck_2002_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_snd_1908_);
lean_inc(v_fst_1907_);
lean_dec(v_snd_1901_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_2002_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v_ref_1912_; lean_object* v_quotContext_1913_; lean_object* v_currMacroScope_1914_; uint8_t v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v_ref_1912_ = lean_ctor_get(v___y_1890_, 2);
v_quotContext_1913_ = lean_ctor_get(v_toCold_1902_, 8);
v_currMacroScope_1914_ = lean_ctor_get(v_toCold_1902_, 9);
v___x_1915_ = 0;
v___x_1916_ = l_Lean_SourceInfo_fromRef(v_ref_1912_, v___x_1915_);
v___x_1917_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1);
v___x_1918_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3));
lean_inc(v_currMacroScope_1914_);
lean_inc(v_quotContext_1913_);
v___x_1919_ = l_Lean_addMacroScope(v_quotContext_1913_, v___x_1918_, v_currMacroScope_1914_);
v___x_1920_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__7));
v___x_1921_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1916_);
lean_ctor_set(v___x_1921_, 1, v___x_1917_);
lean_ctor_set(v___x_1921_, 2, v___x_1919_);
lean_ctor_set(v___x_1921_, 3, v___x_1920_);
lean_inc(v___y_1891_);
lean_inc_ref(v___y_1890_);
lean_inc(v___y_1889_);
lean_inc_ref(v___y_1888_);
lean_inc(v___y_1887_);
lean_inc_ref(v___y_1886_);
v___x_1922_ = lean_apply_8(v_snd_1908_, v___x_1921_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, lean_box(0));
if (lean_obj_tag(v___x_1922_) == 0)
{
lean_object* v_a_1923_; lean_object* v_ctorArgs1_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___x_1971_; uint8_t v___x_1972_; 
v_a_1923_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_a_1923_);
lean_dec_ref_known(v___x_1922_, 1);
v___x_1971_ = lean_array_get_size(v_fst_1903_);
v___x_1972_ = lean_nat_dec_eq(v___x_1971_, v___x_1895_);
if (v___x_1972_ == 0)
{
v_ctorArgs1_1925_ = v_fst_1903_;
v___y_1926_ = v___y_1886_;
v___y_1927_ = v___y_1887_;
v___y_1928_ = v___y_1888_;
v___y_1929_ = v___y_1889_;
v___y_1930_ = v___y_1890_;
v___y_1931_ = v___y_1891_;
goto v___jp_1924_;
}
else
{
lean_object* v___x_1973_; 
lean_inc_ref(v___f_1883_);
lean_inc(v___y_1891_);
lean_inc_ref(v___y_1890_);
lean_inc(v___y_1889_);
lean_inc_ref(v___y_1888_);
lean_inc(v___y_1887_);
lean_inc_ref(v___y_1886_);
v___x_1973_ = lean_apply_7(v___f_1883_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, lean_box(0));
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc_n(v_a_1974_, 7);
lean_dec_ref_known(v___x_1973_, 1);
v___x_1975_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__5));
v___x_1976_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18));
v___x_1977_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__19));
v___x_1978_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1978_, 0, v_a_1974_);
lean_ctor_set(v___x_1978_, 1, v___x_1977_);
v___x_1979_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__21));
v___x_1980_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23);
v___x_1981_ = lean_box(0);
lean_inc(v_currMacroScope_1914_);
lean_inc(v_quotContext_1913_);
v___x_1982_ = l_Lean_addMacroScope(v_quotContext_1913_, v___x_1981_, v_currMacroScope_1914_);
v___x_1983_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__33));
v___x_1984_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1984_, 0, v_a_1974_);
lean_ctor_set(v___x_1984_, 1, v___x_1980_);
lean_ctor_set(v___x_1984_, 2, v___x_1982_);
lean_ctor_set(v___x_1984_, 3, v___x_1983_);
v___x_1985_ = l_Lean_Syntax_node1(v_a_1974_, v___x_1979_, v___x_1984_);
v___x_1986_ = l_Lean_Syntax_node2(v_a_1974_, v___x_1976_, v___x_1978_, v___x_1985_);
v___x_1987_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_1988_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11);
v___x_1989_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1989_, 0, v_a_1974_);
lean_ctor_set(v___x_1989_, 1, v___x_1987_);
lean_ctor_set(v___x_1989_, 2, v___x_1988_);
v___x_1990_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__40));
v___x_1991_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1991_, 0, v_a_1974_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
v___x_1992_ = l_Lean_Syntax_node3(v_a_1974_, v___x_1975_, v___x_1986_, v___x_1989_, v___x_1991_);
v___x_1993_ = lean_array_push(v_fst_1903_, v___x_1992_);
v_ctorArgs1_1925_ = v___x_1993_;
v___y_1926_ = v___y_1886_;
v___y_1927_ = v___y_1887_;
v___y_1928_ = v___y_1888_;
v___y_1929_ = v___y_1889_;
v___y_1930_ = v___y_1890_;
v___y_1931_ = v___y_1891_;
goto v___jp_1924_;
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
lean_dec(v_a_1923_);
lean_del_object(v___x_1910_);
lean_dec(v_fst_1907_);
lean_del_object(v___x_1905_);
lean_dec(v_fst_1903_);
lean_dec_ref(v___f_1883_);
v_a_1994_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1973_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1973_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
v___jp_1924_:
{
lean_object* v___x_1932_; 
lean_inc(v___y_1931_);
lean_inc_ref(v___y_1930_);
lean_inc(v___y_1929_);
lean_inc_ref(v___y_1928_);
lean_inc(v___y_1927_);
lean_inc_ref(v___y_1926_);
v___x_1932_ = lean_apply_7(v___f_1883_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, lean_box(0));
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1962_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1935_ = v___x_1932_;
v_isShared_1936_ = v_isSharedCheck_1962_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1932_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1962_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1940_; 
v___x_1937_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__10));
v___x_1938_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__8));
lean_inc(v_a_1933_);
if (v_isShared_1911_ == 0)
{
lean_ctor_set_tag(v___x_1910_, 2);
lean_ctor_set(v___x_1910_, 1, v___x_1938_);
lean_ctor_set(v___x_1910_, 0, v_a_1933_);
v___x_1940_ = v___x_1910_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1933_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v___x_1938_);
v___x_1940_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1944_; 
v___x_1941_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__0));
v___x_1942_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__1));
lean_inc(v_a_1933_);
if (v_isShared_1906_ == 0)
{
lean_ctor_set_tag(v___x_1905_, 2);
lean_ctor_set(v___x_1905_, 1, v___x_1941_);
lean_ctor_set(v___x_1905_, 0, v_a_1933_);
v___x_1944_ = v___x_1905_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1933_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v___x_1941_);
v___x_1944_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1958_; 
v___x_1945_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__3));
v___x_1946_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_1947_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11);
v___x_1948_ = l_Array_append___redArg(v___x_1947_, v_ctorArgs1_1925_);
lean_dec_ref(v_ctorArgs1_1925_);
v___x_1949_ = l_Array_append___redArg(v___x_1948_, v_fst_1907_);
lean_dec(v_fst_1907_);
lean_inc_n(v_a_1933_, 5);
v___x_1950_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1950_, 0, v_a_1933_);
lean_ctor_set(v___x_1950_, 1, v___x_1946_);
lean_ctor_set(v___x_1950_, 2, v___x_1949_);
v___x_1951_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1951_, 0, v_a_1933_);
lean_ctor_set(v___x_1951_, 1, v___x_1946_);
lean_ctor_set(v___x_1951_, 2, v___x_1947_);
v___x_1952_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__17));
v___x_1953_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1953_, 0, v_a_1933_);
lean_ctor_set(v___x_1953_, 1, v___x_1952_);
v___x_1954_ = l_Lean_Syntax_node4(v_a_1933_, v___x_1945_, v___x_1950_, v___x_1951_, v___x_1953_, v_a_1923_);
v___x_1955_ = l_Lean_Syntax_node2(v_a_1933_, v___x_1942_, v___x_1944_, v___x_1954_);
v___x_1956_ = l_Lean_Syntax_node2(v_a_1933_, v___x_1937_, v___x_1940_, v___x_1955_);
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 0, v___x_1956_);
v___x_1958_ = v___x_1935_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1956_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
lean_dec_ref(v_ctorArgs1_1925_);
lean_dec(v_a_1923_);
lean_del_object(v___x_1910_);
lean_dec(v_fst_1907_);
lean_del_object(v___x_1905_);
v_a_1963_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1932_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1932_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
}
else
{
lean_del_object(v___x_1910_);
lean_dec(v_fst_1907_);
lean_del_object(v___x_1905_);
lean_dec(v_fst_1903_);
lean_dec_ref(v___f_1883_);
return v___x_1922_;
}
}
}
}
else
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
lean_dec_ref(v___f_1883_);
v_a_2005_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2007_ = v___x_1899_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_1899_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
else
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
lean_dec_ref(v___f_1883_);
lean_dec_ref(v___f_1880_);
v_a_2013_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_1893_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_1893_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___boxed(lean_object* v___f_2021_, lean_object* v_numFields_2022_, lean_object* v_indVal_2023_, lean_object* v___f_2024_, lean_object* v_xs_2025_, lean_object* v_type_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2(v___f_2021_, v_numFields_2022_, v_indVal_2023_, v___f_2024_, v_xs_2025_, v_type_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec_ref(v_xs_2025_);
lean_dec_ref(v_indVal_2023_);
lean_dec(v_numFields_2022_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__0(lean_object* v___x_2035_, lean_object* v_ctors_2036_, lean_object* v___f_2037_, lean_object* v_indVal_2038_, lean_object* v___f_2039_, lean_object* v_x_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = l_List_get_x21Internal___redArg(v___x_2035_, v_ctors_2036_, v_x_2040_);
v___x_2049_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0(v___x_2048_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v_toConstantVal_2051_; lean_object* v_numFields_2052_; lean_object* v_type_2053_; lean_object* v___f_2054_; uint8_t v___x_2055_; lean_object* v___x_2056_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref_known(v___x_2049_, 1);
v_toConstantVal_2051_ = lean_ctor_get(v_a_2050_, 0);
lean_inc_ref(v_toConstantVal_2051_);
v_numFields_2052_ = lean_ctor_get(v_a_2050_, 4);
lean_inc(v_numFields_2052_);
lean_dec(v_a_2050_);
v_type_2053_ = lean_ctor_get(v_toConstantVal_2051_, 2);
lean_inc_ref(v_type_2053_);
lean_dec_ref(v_toConstantVal_2051_);
v___f_2054_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___boxed), 13, 4);
lean_closure_set(v___f_2054_, 0, v___f_2037_);
lean_closure_set(v___f_2054_, 1, v_numFields_2052_);
lean_closure_set(v___f_2054_, 2, v_indVal_2038_);
lean_closure_set(v___f_2054_, 3, v___f_2039_);
v___x_2055_ = 0;
v___x_2056_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg(v_type_2053_, v___f_2054_, v___x_2055_, v___x_2055_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_, v___y_2046_);
return v___x_2056_;
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec_ref(v___f_2039_);
lean_dec_ref(v_indVal_2038_);
lean_dec_ref(v___f_2037_);
v_a_2057_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2049_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2049_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__0___boxed(lean_object* v___x_2065_, lean_object* v_ctors_2066_, lean_object* v___f_2067_, lean_object* v_indVal_2068_, lean_object* v___f_2069_, lean_object* v_x_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__0(v___x_2065_, v_ctors_2066_, v___f_2067_, v_indVal_2068_, v___f_2069_, v_x_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v_ctors_2066_);
lean_dec(v___x_2065_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2___redArg(lean_object* v_f_2079_, lean_object* v_n_2080_, lean_object* v_x_2081_, lean_object* v_i_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
uint8_t v___x_2090_; 
v___x_2090_ = lean_nat_dec_lt(v_i_2082_, v_n_2080_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; 
lean_dec(v_i_2082_);
lean_dec_ref(v_f_2079_);
v___x_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2091_, 0, v_x_2081_);
return v___x_2091_;
}
else
{
lean_object* v___x_2092_; 
lean_inc_ref(v_f_2079_);
lean_inc(v___y_2088_);
lean_inc_ref(v___y_2087_);
lean_inc(v___y_2086_);
lean_inc_ref(v___y_2085_);
lean_inc(v___y_2084_);
lean_inc_ref(v___y_2083_);
lean_inc(v_i_2082_);
v___x_2092_ = lean_apply_8(v_f_2079_, v_i_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, lean_box(0));
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v_a_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v_a_2093_ = lean_ctor_get(v___x_2092_, 0);
lean_inc(v_a_2093_);
lean_dec_ref_known(v___x_2092_, 1);
v___x_2094_ = lean_array_push(v_x_2081_, v_a_2093_);
v___x_2095_ = lean_unsigned_to_nat(1u);
v___x_2096_ = lean_nat_add(v_i_2082_, v___x_2095_);
lean_dec(v_i_2082_);
v_x_2081_ = v___x_2094_;
v_i_2082_ = v___x_2096_;
goto _start;
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
lean_dec(v_i_2082_);
lean_dec_ref(v_x_2081_);
lean_dec_ref(v_f_2079_);
v_a_2098_ = lean_ctor_get(v___x_2092_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2100_ = v___x_2092_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2092_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2___redArg___boxed(lean_object* v_f_2106_, lean_object* v_n_2107_, lean_object* v_x_2108_, lean_object* v_i_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2___redArg(v_f_2106_, v_n_2107_, v_x_2108_, v_i_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v_n_2107_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2___redArg(lean_object* v_n_2118_, lean_object* v_f_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v___x_2127_ = lean_mk_empty_array_with_capacity(v_n_2118_);
v___x_2128_ = lean_unsigned_to_nat(0u);
v___x_2129_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2___redArg(v_f_2119_, v_n_2118_, v___x_2127_, v___x_2128_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2___redArg___boxed(lean_object* v_n_2130_, lean_object* v_f_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2___redArg(v_n_2130_, v_f_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v_n_2130_);
return v_res_2139_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__3(void){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2143_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__2));
v___x_2144_ = lean_unsigned_to_nat(2u);
v___x_2145_ = lean_unsigned_to_nat(87u);
v___x_2146_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__1));
v___x_2147_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__0));
v___x_2148_ = l_mkPanicMessageWithDecl(v___x_2147_, v___x_2146_, v___x_2145_, v___x_2144_, v___x_2143_);
return v___x_2148_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__9(void){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__8));
v___x_2160_ = l_String_toRawSubstring_x27(v___x_2159_);
return v___x_2160_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__27(void){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__26));
v___x_2208_ = l_String_toRawSubstring_x27(v___x_2207_);
return v___x_2208_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__37(void){
_start:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2229_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__36));
v___x_2230_ = l_String_toRawSubstring_x27(v___x_2229_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew(lean_object* v_header_2239_, lean_object* v_indVal_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_){
_start:
{
lean_object* v_targetNames_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2444_; 
v_targetNames_2248_ = lean_ctor_get(v_header_2239_, 2);
v_isSharedCheck_2444_ = !lean_is_exclusive(v_header_2239_);
if (v_isSharedCheck_2444_ == 0)
{
lean_object* v_unused_2445_; lean_object* v_unused_2446_; lean_object* v_unused_2447_; 
v_unused_2445_ = lean_ctor_get(v_header_2239_, 3);
lean_dec(v_unused_2445_);
v_unused_2446_ = lean_ctor_get(v_header_2239_, 1);
lean_dec(v_unused_2446_);
v_unused_2447_ = lean_ctor_get(v_header_2239_, 0);
lean_dec(v_unused_2447_);
v___x_2250_ = v_header_2239_;
v_isShared_2251_ = v_isSharedCheck_2444_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_targetNames_2248_);
lean_dec(v_header_2239_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2444_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; uint8_t v___x_2254_; 
v___x_2252_ = lean_array_get_size(v_targetNames_2248_);
v___x_2253_ = lean_unsigned_to_nat(2u);
v___x_2254_ = lean_nat_dec_eq(v___x_2252_, v___x_2253_);
if (v___x_2254_ == 0)
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
lean_del_object(v___x_2250_);
lean_dec_ref(v_targetNames_2248_);
lean_dec_ref(v_indVal_2240_);
v___x_2255_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__3, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__3_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__3);
v___x_2256_ = l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1(v___x_2255_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_);
return v___x_2256_;
}
else
{
lean_object* v_toConstantVal_2257_; lean_object* v_ctors_2258_; lean_object* v_name_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2441_; 
v_toConstantVal_2257_ = lean_ctor_get(v_indVal_2240_, 0);
lean_inc_ref(v_toConstantVal_2257_);
v_ctors_2258_ = lean_ctor_get(v_indVal_2240_, 4);
v_name_2259_ = lean_ctor_get(v_toConstantVal_2257_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v_toConstantVal_2257_);
if (v_isSharedCheck_2441_ == 0)
{
lean_object* v_unused_2442_; lean_object* v_unused_2443_; 
v_unused_2442_ = lean_ctor_get(v_toConstantVal_2257_, 2);
lean_dec(v_unused_2442_);
v_unused_2443_ = lean_ctor_get(v_toConstantVal_2257_, 1);
lean_dec(v_unused_2443_);
v___x_2261_ = v_toConstantVal_2257_;
v_isShared_2262_ = v_isSharedCheck_2441_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_name_2259_);
lean_dec(v_toConstantVal_2257_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2441_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v_ctorIdxName_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
lean_inc_n(v_name_2259_, 2);
v_ctorIdxName_2263_ = l_Lean_mkCtorIdxName(v_name_2259_);
v___x_2264_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__5));
v___x_2265_ = l_Lean_Name_append(v_name_2259_, v___x_2264_);
v___x_2266_ = l_Lean_Core_mkFreshUserName(v___x_2265_, v_a_2245_, v_a_2246_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; lean_object* v___x_2268_; 
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc_n(v_a_2267_, 2);
lean_dec_ref_known(v___x_2266_, 1);
v___x_2268_ = l_Lean_mkCasesOnSameCtor(v_a_2267_, v_name_2259_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v___f_2269_; lean_object* v___f_2270_; lean_object* v___x_2271_; lean_object* v___f_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
lean_dec_ref_known(v___x_2268_, 1);
v___f_2269_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__1));
v___f_2270_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__0));
v___x_2271_ = lean_box(0);
lean_inc_ref(v_indVal_2240_);
lean_inc(v_ctors_2258_);
v___f_2272_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__0___boxed), 13, 5);
lean_closure_set(v___f_2272_, 0, v___x_2271_);
lean_closure_set(v___f_2272_, 1, v_ctors_2258_);
lean_closure_set(v___f_2272_, 2, v___f_2270_);
lean_closure_set(v___f_2272_, 3, v_indVal_2240_);
lean_closure_set(v___f_2272_, 4, v___f_2269_);
v___x_2273_ = l_Lean_InductiveVal_numCtors(v_indVal_2240_);
lean_dec_ref(v_indVal_2240_);
v___x_2274_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2___redArg(v___x_2273_, v___f_2272_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2416_; 
v_a_2275_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2277_ = v___x_2274_;
v_isShared_2278_ = v_isSharedCheck_2416_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2274_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2416_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v_x1_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v_x2_2284_; uint8_t v___x_2285_; 
v___x_2279_ = lean_unsigned_to_nat(0u);
v___x_2280_ = lean_array_get_borrowed(v___x_2271_, v_targetNames_2248_, v___x_2279_);
lean_inc(v___x_2280_);
v_x1_2281_ = l_Lean_mkIdent(v___x_2280_);
v___x_2282_ = lean_unsigned_to_nat(1u);
v___x_2283_ = lean_array_get(v___x_2271_, v_targetNames_2248_, v___x_2282_);
lean_dec_ref(v_targetNames_2248_);
v_x2_2284_ = l_Lean_mkIdent(v___x_2283_);
v___x_2285_ = lean_nat_dec_eq(v___x_2273_, v___x_2282_);
lean_dec(v___x_2273_);
if (v___x_2285_ == 0)
{
lean_object* v_toCold_2286_; lean_object* v_ref_2287_; lean_object* v_quotContext_2288_; lean_object* v_currMacroScope_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2297_; 
v_toCold_2286_ = lean_ctor_get(v_a_2245_, 0);
v_ref_2287_ = lean_ctor_get(v_a_2245_, 2);
v_quotContext_2288_ = lean_ctor_get(v_toCold_2286_, 8);
v_currMacroScope_2289_ = lean_ctor_get(v_toCold_2286_, 9);
v___x_2290_ = l_Lean_SourceInfo_fromRef(v_ref_2287_, v___x_2285_);
v___x_2291_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__0));
v___x_2292_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__1));
lean_inc_n(v___x_2290_, 2);
v___x_2293_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2290_);
lean_ctor_set(v___x_2293_, 1, v___x_2291_);
v___x_2294_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_2295_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11);
if (v_isShared_2262_ == 0)
{
lean_ctor_set_tag(v___x_2261_, 1);
lean_ctor_set(v___x_2261_, 2, v___x_2295_);
lean_ctor_set(v___x_2261_, 1, v___x_2294_);
lean_ctor_set(v___x_2261_, 0, v___x_2290_);
v___x_2297_ = v___x_2261_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v___x_2290_);
lean_ctor_set(v_reuseFailAlloc_2390_, 1, v___x_2294_);
lean_ctor_set(v_reuseFailAlloc_2390_, 2, v___x_2295_);
v___x_2297_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2304_; 
v___x_2298_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__7));
v___x_2299_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__9, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__9_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__9);
v___x_2300_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__10));
lean_inc(v_currMacroScope_2289_);
lean_inc(v_quotContext_2288_);
v___x_2301_ = l_Lean_addMacroScope(v_quotContext_2288_, v___x_2300_, v_currMacroScope_2289_);
v___x_2302_ = lean_box(0);
lean_inc(v___x_2290_);
if (v_isShared_2251_ == 0)
{
lean_ctor_set_tag(v___x_2250_, 3);
lean_ctor_set(v___x_2250_, 3, v___x_2302_);
lean_ctor_set(v___x_2250_, 2, v___x_2301_);
lean_ctor_set(v___x_2250_, 1, v___x_2299_);
lean_ctor_set(v___x_2250_, 0, v___x_2290_);
v___x_2304_ = v___x_2250_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2290_);
lean_ctor_set(v_reuseFailAlloc_2389_, 1, v___x_2299_);
lean_ctor_set(v_reuseFailAlloc_2389_, 2, v___x_2301_);
lean_ctor_set(v_reuseFailAlloc_2389_, 3, v___x_2302_);
v___x_2304_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2387_; 
v___x_2305_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__11));
lean_inc_n(v___x_2290_, 41);
v___x_2306_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2290_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
lean_inc_ref(v___x_2304_);
v___x_2307_ = l_Lean_Syntax_node2(v___x_2290_, v___x_2294_, v___x_2304_, v___x_2306_);
v___x_2308_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3));
v___x_2309_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35);
v___x_2310_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__36));
lean_inc_n(v_currMacroScope_2289_, 6);
lean_inc_n(v_quotContext_2288_, 6);
v___x_2311_ = l_Lean_addMacroScope(v_quotContext_2288_, v___x_2310_, v_currMacroScope_2289_);
v___x_2312_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__13));
v___x_2313_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2290_);
lean_ctor_set(v___x_2313_, 1, v___x_2309_);
lean_ctor_set(v___x_2313_, 2, v___x_2311_);
lean_ctor_set(v___x_2313_, 3, v___x_2312_);
v___x_2314_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__16));
v___x_2315_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18));
v___x_2316_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__19));
v___x_2317_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2290_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
v___x_2318_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__21));
v___x_2319_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23);
v___x_2320_ = l_Lean_addMacroScope(v_quotContext_2288_, v___x_2271_, v_currMacroScope_2289_);
v___x_2321_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__16));
v___x_2322_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2290_);
lean_ctor_set(v___x_2322_, 1, v___x_2319_);
lean_ctor_set(v___x_2322_, 2, v___x_2320_);
lean_ctor_set(v___x_2322_, 3, v___x_2321_);
v___x_2323_ = l_Lean_Syntax_node1(v___x_2290_, v___x_2318_, v___x_2322_);
v___x_2324_ = l_Lean_Syntax_node2(v___x_2290_, v___x_2315_, v___x_2317_, v___x_2323_);
v___x_2325_ = l_Lean_mkCIdent(v_ctorIdxName_2263_);
lean_inc(v_x1_2281_);
v___x_2326_ = l_Lean_Syntax_node1(v___x_2290_, v___x_2294_, v_x1_2281_);
lean_inc(v___x_2325_);
v___x_2327_ = l_Lean_Syntax_node2(v___x_2290_, v___x_2308_, v___x_2325_, v___x_2326_);
v___x_2328_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__40));
v___x_2329_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2290_);
lean_ctor_set(v___x_2329_, 1, v___x_2328_);
lean_inc_ref_n(v___x_2329_, 2);
lean_inc_n(v___x_2324_, 2);
v___x_2330_ = l_Lean_Syntax_node3(v___x_2290_, v___x_2314_, v___x_2324_, v___x_2327_, v___x_2329_);
lean_inc(v_x2_2284_);
v___x_2331_ = l_Lean_Syntax_node1(v___x_2290_, v___x_2294_, v_x2_2284_);
v___x_2332_ = l_Lean_Syntax_node2(v___x_2290_, v___x_2308_, v___x_2325_, v___x_2331_);
v___x_2333_ = l_Lean_Syntax_node3(v___x_2290_, v___x_2314_, v___x_2324_, v___x_2332_, v___x_2329_);
v___x_2334_ = l_Lean_Syntax_node2(v___x_2290_, v___x_2294_, v___x_2330_, v___x_2333_);
v___x_2335_ = l_Lean_Syntax_node2(v___x_2290_, v___x_2308_, v___x_2313_, v___x_2334_);
v___x_2336_ = l_Lean_Syntax_node2(v___x_2290_, v___x_2298_, v___x_2307_, v___x_2335_);
v___x_2337_ = l_Lean_Syntax_node1(v___x_2290_, v___x_2294_, v___x_2336_);
v___x_2338_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__2));
v___x_2339_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2290_);
lean_ctor_set(v___x_2339_, 1, v___x_2338_);
v___x_2340_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__4));
v___x_2341_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__25));
v___x_2342_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__12));
v___x_2343_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2290_);
lean_ctor_set(v___x_2343_, 1, v___x_2342_);
v___x_2344_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__20, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__20_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__20);
v___x_2345_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__16));
v___x_2346_ = l_Lean_addMacroScope(v_quotContext_2288_, v___x_2345_, v_currMacroScope_2289_);
v___x_2347_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__19));
v___x_2348_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2290_);
lean_ctor_set(v___x_2348_, 1, v___x_2344_);
lean_ctor_set(v___x_2348_, 2, v___x_2346_);
lean_ctor_set(v___x_2348_, 3, v___x_2347_);
lean_inc_ref(v___x_2348_);
v___x_2349_ = l_Lean_Syntax_node1(v___x_2290_, v___x_2294_, v___x_2348_);
v___x_2350_ = l_Lean_Syntax_node1(v___x_2290_, v___x_2294_, v___x_2349_);
v___x_2351_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__17));
v___x_2352_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2290_);
lean_ctor_set(v___x_2352_, 1, v___x_2351_);
lean_inc_ref_n(v___x_2352_, 2);
lean_inc_ref_n(v___x_2343_, 2);
v___x_2353_ = l_Lean_Syntax_node4(v___x_2290_, v___x_2341_, v___x_2343_, v___x_2350_, v___x_2352_, v___x_2348_);
v___x_2354_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__27, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__27_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__27);
v___x_2355_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__29));
v___x_2356_ = l_Lean_addMacroScope(v_quotContext_2288_, v___x_2355_, v_currMacroScope_2289_);
v___x_2357_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__22));
v___x_2358_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2290_);
lean_ctor_set(v___x_2358_, 1, v___x_2354_);
lean_ctor_set(v___x_2358_, 2, v___x_2356_);
lean_ctor_set(v___x_2358_, 3, v___x_2357_);
lean_inc_ref(v___x_2358_);
v___x_2359_ = l_Lean_Syntax_node1(v___x_2290_, v___x_2294_, v___x_2358_);
v___x_2360_ = l_Lean_Syntax_node1(v___x_2290_, v___x_2294_, v___x_2359_);
v___x_2361_ = l_Lean_Syntax_node4(v___x_2290_, v___x_2341_, v___x_2343_, v___x_2360_, v___x_2352_, v___x_2358_);
v___x_2362_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1);
v___x_2363_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3));
v___x_2364_ = l_Lean_addMacroScope(v_quotContext_2288_, v___x_2363_, v_currMacroScope_2289_);
v___x_2365_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__25));
v___x_2366_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2290_);
lean_ctor_set(v___x_2366_, 1, v___x_2362_);
lean_ctor_set(v___x_2366_, 2, v___x_2364_);
lean_ctor_set(v___x_2366_, 3, v___x_2365_);
v___x_2367_ = l_Lean_Syntax_node1(v___x_2290_, v___x_2294_, v___x_2366_);
v___x_2368_ = l_Lean_Syntax_node1(v___x_2290_, v___x_2294_, v___x_2367_);
v___x_2369_ = l_Lean_mkCIdent(v_a_2267_);
v___x_2370_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__27, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__27_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__27);
v___x_2371_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__31));
v___x_2372_ = l_Lean_addMacroScope(v_quotContext_2288_, v___x_2371_, v_currMacroScope_2289_);
v___x_2373_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__35));
v___x_2374_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2290_);
lean_ctor_set(v___x_2374_, 1, v___x_2370_);
lean_ctor_set(v___x_2374_, 2, v___x_2372_);
lean_ctor_set(v___x_2374_, 3, v___x_2373_);
v___x_2375_ = l_Lean_Syntax_node1(v___x_2290_, v___x_2294_, v___x_2304_);
v___x_2376_ = l_Lean_Syntax_node2(v___x_2290_, v___x_2308_, v___x_2374_, v___x_2375_);
v___x_2377_ = l_Lean_Syntax_node3(v___x_2290_, v___x_2314_, v___x_2324_, v___x_2376_, v___x_2329_);
v___x_2378_ = l_Array_mkArray3___redArg(v_x1_2281_, v_x2_2284_, v___x_2377_);
v___x_2379_ = l_Array_append___redArg(v___x_2378_, v_a_2275_);
lean_dec(v_a_2275_);
v___x_2380_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2290_);
lean_ctor_set(v___x_2380_, 1, v___x_2294_);
lean_ctor_set(v___x_2380_, 2, v___x_2379_);
v___x_2381_ = l_Lean_Syntax_node2(v___x_2290_, v___x_2308_, v___x_2369_, v___x_2380_);
v___x_2382_ = l_Lean_Syntax_node4(v___x_2290_, v___x_2341_, v___x_2343_, v___x_2368_, v___x_2352_, v___x_2381_);
v___x_2383_ = l_Lean_Syntax_node3(v___x_2290_, v___x_2294_, v___x_2353_, v___x_2361_, v___x_2382_);
v___x_2384_ = l_Lean_Syntax_node1(v___x_2290_, v___x_2340_, v___x_2383_);
lean_inc_ref(v___x_2297_);
v___x_2385_ = l_Lean_Syntax_node6(v___x_2290_, v___x_2292_, v___x_2293_, v___x_2297_, v___x_2297_, v___x_2337_, v___x_2339_, v___x_2384_);
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 0, v___x_2385_);
v___x_2387_ = v___x_2277_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2385_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
else
{
lean_object* v_toCold_2391_; lean_object* v_ref_2392_; lean_object* v_quotContext_2393_; lean_object* v_currMacroScope_2394_; uint8_t v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2405_; 
lean_dec(v_ctorIdxName_2263_);
v_toCold_2391_ = lean_ctor_get(v_a_2245_, 0);
v_ref_2392_ = lean_ctor_get(v_a_2245_, 2);
v_quotContext_2393_ = lean_ctor_get(v_toCold_2391_, 8);
v_currMacroScope_2394_ = lean_ctor_get(v_toCold_2391_, 9);
v___x_2395_ = 0;
v___x_2396_ = l_Lean_SourceInfo_fromRef(v_ref_2392_, v___x_2395_);
v___x_2397_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3));
v___x_2398_ = l_Lean_mkCIdent(v_a_2267_);
v___x_2399_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_2400_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__37, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__37_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__37);
v___x_2401_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__38));
lean_inc(v_currMacroScope_2394_);
lean_inc(v_quotContext_2393_);
v___x_2402_ = l_Lean_addMacroScope(v_quotContext_2393_, v___x_2401_, v_currMacroScope_2394_);
v___x_2403_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__40));
lean_inc(v___x_2396_);
if (v_isShared_2251_ == 0)
{
lean_ctor_set_tag(v___x_2250_, 3);
lean_ctor_set(v___x_2250_, 3, v___x_2403_);
lean_ctor_set(v___x_2250_, 2, v___x_2402_);
lean_ctor_set(v___x_2250_, 1, v___x_2400_);
lean_ctor_set(v___x_2250_, 0, v___x_2396_);
v___x_2405_ = v___x_2250_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2396_);
lean_ctor_set(v_reuseFailAlloc_2415_, 1, v___x_2400_);
lean_ctor_set(v_reuseFailAlloc_2415_, 2, v___x_2402_);
lean_ctor_set(v_reuseFailAlloc_2415_, 3, v___x_2403_);
v___x_2405_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2409_; 
v___x_2406_ = l_Array_mkArray3___redArg(v_x1_2281_, v_x2_2284_, v___x_2405_);
v___x_2407_ = l_Array_append___redArg(v___x_2406_, v_a_2275_);
lean_dec(v_a_2275_);
lean_inc(v___x_2396_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set_tag(v___x_2261_, 1);
lean_ctor_set(v___x_2261_, 2, v___x_2407_);
lean_ctor_set(v___x_2261_, 1, v___x_2399_);
lean_ctor_set(v___x_2261_, 0, v___x_2396_);
v___x_2409_ = v___x_2261_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___x_2396_);
lean_ctor_set(v_reuseFailAlloc_2414_, 1, v___x_2399_);
lean_ctor_set(v_reuseFailAlloc_2414_, 2, v___x_2407_);
v___x_2409_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
lean_object* v___x_2410_; lean_object* v___x_2412_; 
v___x_2410_ = l_Lean_Syntax_node2(v___x_2396_, v___x_2397_, v___x_2398_, v___x_2409_);
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 0, v___x_2410_);
v___x_2412_ = v___x_2277_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v___x_2410_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
}
}
else
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2424_; 
lean_dec(v___x_2273_);
lean_dec(v_a_2267_);
lean_dec(v_ctorIdxName_2263_);
lean_del_object(v___x_2261_);
lean_del_object(v___x_2250_);
lean_dec_ref(v_targetNames_2248_);
v_a_2417_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2419_ = v___x_2274_;
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2274_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2422_; 
if (v_isShared_2420_ == 0)
{
v___x_2422_ = v___x_2419_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2417_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
else
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
lean_dec(v_a_2267_);
lean_dec(v_ctorIdxName_2263_);
lean_del_object(v___x_2261_);
lean_del_object(v___x_2250_);
lean_dec_ref(v_targetNames_2248_);
lean_dec_ref(v_indVal_2240_);
v_a_2425_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2427_ = v___x_2268_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2268_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2425_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
else
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
lean_dec(v_ctorIdxName_2263_);
lean_del_object(v___x_2261_);
lean_dec(v_name_2259_);
lean_del_object(v___x_2250_);
lean_dec_ref(v_targetNames_2248_);
lean_dec_ref(v_indVal_2240_);
v_a_2433_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___x_2266_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2266_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___boxed(lean_object* v_header_2448_, lean_object* v_indVal_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew(v_header_2448_, v_indVal_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_);
lean_dec(v_a_2455_);
lean_dec_ref(v_a_2454_);
lean_dec(v_a_2453_);
lean_dec_ref(v_a_2452_);
lean_dec(v_a_2451_);
lean_dec_ref(v_a_2450_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0(lean_object* v_upperBound_2458_, lean_object* v_indVal_2459_, lean_object* v_xs_2460_, lean_object* v_a_2461_, lean_object* v_inst_2462_, lean_object* v_R_2463_, lean_object* v_a_2464_, lean_object* v_b_2465_, lean_object* v_c_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg(v_upperBound_2458_, v_indVal_2459_, v_xs_2460_, v_a_2461_, v_a_2464_, v_b_2465_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___boxed(lean_object* v_upperBound_2475_, lean_object* v_indVal_2476_, lean_object* v_xs_2477_, lean_object* v_a_2478_, lean_object* v_inst_2479_, lean_object* v_R_2480_, lean_object* v_a_2481_, lean_object* v_b_2482_, lean_object* v_c_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0(v_upperBound_2475_, v_indVal_2476_, v_xs_2477_, v_a_2478_, v_inst_2479_, v_R_2480_, v_a_2481_, v_b_2482_, v_c_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec_ref(v_a_2478_);
lean_dec_ref(v_xs_2477_);
lean_dec_ref(v_indVal_2476_);
lean_dec(v_upperBound_2475_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2(lean_object* v_00_u03b1_2492_, lean_object* v_n_2493_, lean_object* v_f_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_){
_start:
{
lean_object* v___x_2502_; 
v___x_2502_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2___redArg(v_n_2493_, v_f_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
return v___x_2502_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2___boxed(lean_object* v_00_u03b1_2503_, lean_object* v_n_2504_, lean_object* v_f_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2(v_00_u03b1_2503_, v_n_2504_, v_f_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v_n_2504_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2(lean_object* v_00_u03b1_2514_, lean_object* v_f_2515_, lean_object* v_n_2516_, lean_object* v_x_2517_, lean_object* v_i_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v___x_2526_; 
v___x_2526_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2___redArg(v_f_2515_, v_n_2516_, v_x_2517_, v_i_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2___boxed(lean_object* v_00_u03b1_2527_, lean_object* v_f_2528_, lean_object* v_n_2529_, lean_object* v_x_2530_, lean_object* v_i_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2(v_00_u03b1_2527_, v_f_2528_, v_n_2529_, v_x_2530_, v_i_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v_n_2529_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch_spec__0(lean_object* v_opts_2540_, lean_object* v_opt_2541_){
_start:
{
lean_object* v_name_2542_; lean_object* v_defValue_2543_; lean_object* v_map_2544_; lean_object* v___x_2545_; 
v_name_2542_ = lean_ctor_get(v_opt_2541_, 0);
v_defValue_2543_ = lean_ctor_get(v_opt_2541_, 1);
v_map_2544_ = lean_ctor_get(v_opts_2540_, 0);
v___x_2545_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2544_, v_name_2542_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_inc(v_defValue_2543_);
return v_defValue_2543_;
}
else
{
lean_object* v_val_2546_; 
v_val_2546_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_val_2546_);
lean_dec_ref_known(v___x_2545_, 1);
if (lean_obj_tag(v_val_2546_) == 3)
{
lean_object* v_v_2547_; 
v_v_2547_ = lean_ctor_get(v_val_2546_, 0);
lean_inc(v_v_2547_);
lean_dec_ref_known(v_val_2546_, 1);
return v_v_2547_;
}
else
{
lean_dec(v_val_2546_);
lean_inc(v_defValue_2543_);
return v_defValue_2543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch_spec__0___boxed(lean_object* v_opts_2548_, lean_object* v_opt_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch_spec__0(v_opts_2548_, v_opt_2549_);
lean_dec_ref(v_opt_2549_);
lean_dec_ref(v_opts_2548_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch(lean_object* v_header_2551_, lean_object* v_indVal_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_){
_start:
{
lean_object* v_toCold_2560_; lean_object* v_options_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; uint8_t v___x_2565_; 
v_toCold_2560_ = lean_ctor_get(v_a_2557_, 0);
v_options_2561_ = lean_ctor_get(v_toCold_2560_, 2);
v___x_2562_ = l___private_Lean_Elab_Deriving_Ord_0__deriving_ord_linear__construction__threshold;
v___x_2563_ = l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch_spec__0(v_options_2561_, v___x_2562_);
v___x_2564_ = l_Lean_InductiveVal_numCtors(v_indVal_2552_);
v___x_2565_ = lean_nat_dec_le(v___x_2563_, v___x_2564_);
lean_dec(v___x_2564_);
lean_dec(v___x_2563_);
if (v___x_2565_ == 0)
{
lean_object* v___x_2566_; 
v___x_2566_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld(v_header_2551_, v_indVal_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_);
return v___x_2566_;
}
else
{
lean_object* v___x_2567_; 
v___x_2567_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew(v_header_2551_, v_indVal_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_);
return v___x_2567_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch___boxed(lean_object* v_header_2568_, lean_object* v_indVal_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch(v_header_2568_, v_indVal_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_);
lean_dec(v_a_2575_);
lean_dec_ref(v_a_2574_);
lean_dec(v_a_2573_);
lean_dec_ref(v_a_2572_);
lean_dec(v_a_2571_);
lean_dec_ref(v_a_2570_);
return v_res_2577_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14(void){
_start:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2616_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__6));
v___x_2617_ = l_String_toRawSubstring_x27(v___x_2616_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction(lean_object* v_ctx_2651_, lean_object* v_i_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_){
_start:
{
lean_object* v_typeInfos_2660_; lean_object* v_auxFunNames_2661_; uint8_t v_usePartial_2662_; lean_object* v___x_2663_; lean_object* v_indVal_2664_; lean_object* v___x_2665_; 
v_typeInfos_2660_ = lean_ctor_get(v_ctx_2651_, 1);
v_auxFunNames_2661_ = lean_ctor_get(v_ctx_2651_, 2);
v_usePartial_2662_ = lean_ctor_get_uint8(v_ctx_2651_, sizeof(void*)*3);
v___x_2663_ = l_Lean_instInhabitedInductiveVal_default;
v_indVal_2664_ = lean_array_get_borrowed(v___x_2663_, v_typeInfos_2660_, v_i_2652_);
lean_inc(v_indVal_2664_);
v___x_2665_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader(v_indVal_2664_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; lean_object* v___x_2667_; 
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc_n(v_a_2666_, 2);
lean_dec_ref_known(v___x_2665_, 1);
lean_inc(v_indVal_2664_);
v___x_2667_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch(v_a_2666_, v_indVal_2664_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2801_; 
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2670_ = v___x_2667_;
v_isShared_2671_ = v_isSharedCheck_2801_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2667_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2801_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2672_; lean_object* v_auxFunName_2673_; lean_object* v_body_2675_; lean_object* v___y_2676_; 
v___x_2672_ = lean_box(0);
v_auxFunName_2673_ = lean_array_get_borrowed(v___x_2672_, v_auxFunNames_2661_, v_i_2652_);
if (v_usePartial_2662_ == 0)
{
v_body_2675_ = v_a_2668_;
v___y_2676_ = v_a_2657_;
goto v___jp_2674_;
}
else
{
lean_object* v_argNames_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
v_argNames_2787_ = lean_ctor_get(v_a_2666_, 1);
v___x_2788_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader___closed__0));
lean_inc_ref(v_argNames_2787_);
v___x_2789_ = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(v_ctx_2651_, v___x_2788_, v_argNames_2787_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; lean_object* v___x_2791_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2790_);
lean_dec_ref_known(v___x_2789_, 1);
v___x_2791_ = l_Lean_Elab_Deriving_mkLet(v_a_2790_, v_a_2668_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_);
lean_dec(v_a_2790_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_a_2792_);
lean_dec_ref_known(v___x_2791_, 1);
v_body_2675_ = v_a_2792_;
v___y_2676_ = v_a_2657_;
goto v___jp_2674_;
}
else
{
lean_del_object(v___x_2670_);
lean_dec(v_a_2666_);
return v___x_2791_;
}
}
else
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
lean_del_object(v___x_2670_);
lean_dec(v_a_2668_);
lean_dec(v_a_2666_);
v_a_2793_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v___x_2789_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2789_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2793_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
v___jp_2674_:
{
if (v_usePartial_2662_ == 0)
{
lean_object* v_toCold_2677_; lean_object* v_binders_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2725_; 
v_toCold_2677_ = lean_ctor_get(v___y_2676_, 0);
v_binders_2678_ = lean_ctor_get(v_a_2666_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v_a_2666_);
if (v_isSharedCheck_2725_ == 0)
{
lean_object* v_unused_2726_; lean_object* v_unused_2727_; lean_object* v_unused_2728_; 
v_unused_2726_ = lean_ctor_get(v_a_2666_, 3);
lean_dec(v_unused_2726_);
v_unused_2727_ = lean_ctor_get(v_a_2666_, 2);
lean_dec(v_unused_2727_);
v_unused_2728_ = lean_ctor_get(v_a_2666_, 1);
lean_dec(v_unused_2728_);
v___x_2680_ = v_a_2666_;
v_isShared_2681_ = v_isSharedCheck_2725_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_binders_2678_);
lean_dec(v_a_2666_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2725_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v_ref_2682_; lean_object* v_quotContext_2683_; lean_object* v_currMacroScope_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2709_; 
v_ref_2682_ = lean_ctor_get(v___y_2676_, 2);
v_quotContext_2683_ = lean_ctor_get(v_toCold_2677_, 8);
v_currMacroScope_2684_ = lean_ctor_get(v_toCold_2677_, 9);
v___x_2685_ = l_Lean_SourceInfo_fromRef(v_ref_2682_, v_usePartial_2662_);
v___x_2686_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__2));
v___x_2687_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__4));
v___x_2688_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_2689_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11);
lean_inc_n(v___x_2685_, 7);
v___x_2690_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2685_);
lean_ctor_set(v___x_2690_, 1, v___x_2688_);
lean_ctor_set(v___x_2690_, 2, v___x_2689_);
lean_inc_ref_n(v___x_2690_, 8);
v___x_2691_ = l_Lean_Syntax_node7(v___x_2685_, v___x_2687_, v___x_2690_, v___x_2690_, v___x_2690_, v___x_2690_, v___x_2690_, v___x_2690_, v___x_2690_);
v___x_2692_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__6));
v___x_2693_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__7));
v___x_2694_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2685_);
lean_ctor_set(v___x_2694_, 1, v___x_2693_);
v___x_2695_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__9));
lean_inc(v_auxFunName_2673_);
v___x_2696_ = l_Lean_mkIdent(v_auxFunName_2673_);
v___x_2697_ = l_Lean_Syntax_node2(v___x_2685_, v___x_2695_, v___x_2696_, v___x_2690_);
v___x_2698_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__11));
v___x_2699_ = l_Array_append___redArg(v___x_2689_, v_binders_2678_);
lean_dec_ref(v_binders_2678_);
v___x_2700_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2685_);
lean_ctor_set(v___x_2700_, 1, v___x_2688_);
lean_ctor_set(v___x_2700_, 2, v___x_2699_);
v___x_2701_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__13));
v___x_2702_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__11));
v___x_2703_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2685_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
v___x_2704_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14);
v___x_2705_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__15));
lean_inc(v_currMacroScope_2684_);
lean_inc(v_quotContext_2683_);
v___x_2706_ = l_Lean_addMacroScope(v_quotContext_2683_, v___x_2705_, v_currMacroScope_2684_);
v___x_2707_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__19));
if (v_isShared_2681_ == 0)
{
lean_ctor_set_tag(v___x_2680_, 3);
lean_ctor_set(v___x_2680_, 3, v___x_2707_);
lean_ctor_set(v___x_2680_, 2, v___x_2706_);
lean_ctor_set(v___x_2680_, 1, v___x_2704_);
lean_ctor_set(v___x_2680_, 0, v___x_2685_);
v___x_2709_ = v___x_2680_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2685_);
lean_ctor_set(v_reuseFailAlloc_2724_, 1, v___x_2704_);
lean_ctor_set(v_reuseFailAlloc_2724_, 2, v___x_2706_);
lean_ctor_set(v_reuseFailAlloc_2724_, 3, v___x_2707_);
v___x_2709_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2722_; 
lean_inc_n(v___x_2685_, 7);
v___x_2710_ = l_Lean_Syntax_node2(v___x_2685_, v___x_2701_, v___x_2703_, v___x_2709_);
v___x_2711_ = l_Lean_Syntax_node1(v___x_2685_, v___x_2688_, v___x_2710_);
v___x_2712_ = l_Lean_Syntax_node2(v___x_2685_, v___x_2698_, v___x_2700_, v___x_2711_);
v___x_2713_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__21));
v___x_2714_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__22));
v___x_2715_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2685_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
v___x_2716_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__25));
lean_inc_ref_n(v___x_2690_, 3);
v___x_2717_ = l_Lean_Syntax_node2(v___x_2685_, v___x_2716_, v___x_2690_, v___x_2690_);
v___x_2718_ = l_Lean_Syntax_node4(v___x_2685_, v___x_2713_, v___x_2715_, v_body_2675_, v___x_2717_, v___x_2690_);
v___x_2719_ = l_Lean_Syntax_node5(v___x_2685_, v___x_2692_, v___x_2694_, v___x_2697_, v___x_2712_, v___x_2718_, v___x_2690_);
v___x_2720_ = l_Lean_Syntax_node2(v___x_2685_, v___x_2686_, v___x_2691_, v___x_2719_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 0, v___x_2720_);
v___x_2722_ = v___x_2670_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v___x_2720_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
else
{
lean_object* v_toCold_2729_; lean_object* v_binders_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2783_; 
v_toCold_2729_ = lean_ctor_get(v___y_2676_, 0);
v_binders_2730_ = lean_ctor_get(v_a_2666_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v_a_2666_);
if (v_isSharedCheck_2783_ == 0)
{
lean_object* v_unused_2784_; lean_object* v_unused_2785_; lean_object* v_unused_2786_; 
v_unused_2784_ = lean_ctor_get(v_a_2666_, 3);
lean_dec(v_unused_2784_);
v_unused_2785_ = lean_ctor_get(v_a_2666_, 2);
lean_dec(v_unused_2785_);
v_unused_2786_ = lean_ctor_get(v_a_2666_, 1);
lean_dec(v_unused_2786_);
v___x_2732_ = v_a_2666_;
v_isShared_2733_ = v_isSharedCheck_2783_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_binders_2730_);
lean_dec(v_a_2666_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2783_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v_ref_2734_; lean_object* v_quotContext_2735_; lean_object* v_currMacroScope_2736_; uint8_t v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2767_; 
v_ref_2734_ = lean_ctor_get(v___y_2676_, 2);
v_quotContext_2735_ = lean_ctor_get(v_toCold_2729_, 8);
v_currMacroScope_2736_ = lean_ctor_get(v_toCold_2729_, 9);
v___x_2737_ = 0;
v___x_2738_ = l_Lean_SourceInfo_fromRef(v_ref_2734_, v___x_2737_);
v___x_2739_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__2));
v___x_2740_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__4));
v___x_2741_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_2742_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11);
lean_inc_n(v___x_2738_, 10);
v___x_2743_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2738_);
lean_ctor_set(v___x_2743_, 1, v___x_2741_);
lean_ctor_set(v___x_2743_, 2, v___x_2742_);
v___x_2744_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__26));
v___x_2745_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__27));
v___x_2746_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2738_);
lean_ctor_set(v___x_2746_, 1, v___x_2744_);
v___x_2747_ = l_Lean_Syntax_node1(v___x_2738_, v___x_2745_, v___x_2746_);
v___x_2748_ = l_Lean_Syntax_node1(v___x_2738_, v___x_2741_, v___x_2747_);
lean_inc_ref_n(v___x_2743_, 7);
v___x_2749_ = l_Lean_Syntax_node7(v___x_2738_, v___x_2740_, v___x_2743_, v___x_2743_, v___x_2743_, v___x_2743_, v___x_2743_, v___x_2743_, v___x_2748_);
v___x_2750_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__6));
v___x_2751_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__7));
v___x_2752_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2738_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
v___x_2753_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__9));
lean_inc(v_auxFunName_2673_);
v___x_2754_ = l_Lean_mkIdent(v_auxFunName_2673_);
v___x_2755_ = l_Lean_Syntax_node2(v___x_2738_, v___x_2753_, v___x_2754_, v___x_2743_);
v___x_2756_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__11));
v___x_2757_ = l_Array_append___redArg(v___x_2742_, v_binders_2730_);
lean_dec_ref(v_binders_2730_);
v___x_2758_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2738_);
lean_ctor_set(v___x_2758_, 1, v___x_2741_);
lean_ctor_set(v___x_2758_, 2, v___x_2757_);
v___x_2759_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__13));
v___x_2760_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__11));
v___x_2761_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2738_);
lean_ctor_set(v___x_2761_, 1, v___x_2760_);
v___x_2762_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14);
v___x_2763_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__15));
lean_inc(v_currMacroScope_2736_);
lean_inc(v_quotContext_2735_);
v___x_2764_ = l_Lean_addMacroScope(v_quotContext_2735_, v___x_2763_, v_currMacroScope_2736_);
v___x_2765_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__19));
if (v_isShared_2733_ == 0)
{
lean_ctor_set_tag(v___x_2732_, 3);
lean_ctor_set(v___x_2732_, 3, v___x_2765_);
lean_ctor_set(v___x_2732_, 2, v___x_2764_);
lean_ctor_set(v___x_2732_, 1, v___x_2762_);
lean_ctor_set(v___x_2732_, 0, v___x_2738_);
v___x_2767_ = v___x_2732_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v___x_2738_);
lean_ctor_set(v_reuseFailAlloc_2782_, 1, v___x_2762_);
lean_ctor_set(v_reuseFailAlloc_2782_, 2, v___x_2764_);
lean_ctor_set(v_reuseFailAlloc_2782_, 3, v___x_2765_);
v___x_2767_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2780_; 
lean_inc_n(v___x_2738_, 7);
v___x_2768_ = l_Lean_Syntax_node2(v___x_2738_, v___x_2759_, v___x_2761_, v___x_2767_);
v___x_2769_ = l_Lean_Syntax_node1(v___x_2738_, v___x_2741_, v___x_2768_);
v___x_2770_ = l_Lean_Syntax_node2(v___x_2738_, v___x_2756_, v___x_2758_, v___x_2769_);
v___x_2771_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__21));
v___x_2772_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__22));
v___x_2773_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2738_);
lean_ctor_set(v___x_2773_, 1, v___x_2772_);
v___x_2774_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__25));
lean_inc_ref_n(v___x_2743_, 3);
v___x_2775_ = l_Lean_Syntax_node2(v___x_2738_, v___x_2774_, v___x_2743_, v___x_2743_);
v___x_2776_ = l_Lean_Syntax_node4(v___x_2738_, v___x_2771_, v___x_2773_, v_body_2675_, v___x_2775_, v___x_2743_);
v___x_2777_ = l_Lean_Syntax_node5(v___x_2738_, v___x_2750_, v___x_2752_, v___x_2755_, v___x_2770_, v___x_2776_, v___x_2743_);
v___x_2778_ = l_Lean_Syntax_node2(v___x_2738_, v___x_2739_, v___x_2749_, v___x_2777_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 0, v___x_2778_);
v___x_2780_ = v___x_2670_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v___x_2778_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2666_);
return v___x_2667_;
}
}
else
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
v_a_2802_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2665_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2665_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2805_ == 0)
{
v___x_2807_ = v___x_2804_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2802_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___boxed(lean_object* v_ctx_2810_, lean_object* v_i_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_){
_start:
{
lean_object* v_res_2819_; 
v_res_2819_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction(v_ctx_2810_, v_i_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_);
lean_dec(v_a_2817_);
lean_dec_ref(v_a_2816_);
lean_dec(v_a_2815_);
lean_dec_ref(v_a_2814_);
lean_dec(v_a_2813_);
lean_dec_ref(v_a_2812_);
lean_dec(v_i_2811_);
lean_dec_ref(v_ctx_2810_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0___redArg(lean_object* v_upperBound_2820_, lean_object* v_ctx_2821_, lean_object* v_a_2822_, lean_object* v_b_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
uint8_t v___x_2831_; 
v___x_2831_ = lean_nat_dec_lt(v_a_2822_, v_upperBound_2820_);
if (v___x_2831_ == 0)
{
lean_object* v___x_2832_; 
lean_dec(v_a_2822_);
v___x_2832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2832_, 0, v_b_2823_);
return v___x_2832_;
}
else
{
lean_object* v___x_2833_; 
v___x_2833_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction(v_ctx_2821_, v_a_2822_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
lean_inc(v_a_2834_);
lean_dec_ref_known(v___x_2833_, 1);
v___x_2835_ = lean_array_push(v_b_2823_, v_a_2834_);
v___x_2836_ = lean_unsigned_to_nat(1u);
v___x_2837_ = lean_nat_add(v_a_2822_, v___x_2836_);
lean_dec(v_a_2822_);
v_a_2822_ = v___x_2837_;
v_b_2823_ = v___x_2835_;
goto _start;
}
else
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2846_; 
lean_dec_ref(v_b_2823_);
lean_dec(v_a_2822_);
v_a_2839_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2841_ = v___x_2833_;
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2833_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2844_; 
if (v_isShared_2842_ == 0)
{
v___x_2844_ = v___x_2841_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2839_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0___redArg___boxed(lean_object* v_upperBound_2847_, lean_object* v_ctx_2848_, lean_object* v_a_2849_, lean_object* v_b_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
lean_object* v_res_2858_; 
v_res_2858_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0___redArg(v_upperBound_2847_, v_ctx_2848_, v_a_2849_, v_b_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_);
lean_dec(v___y_2856_);
lean_dec_ref(v___y_2855_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec_ref(v_ctx_2848_);
lean_dec(v_upperBound_2847_);
return v_res_2858_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__5(void){
_start:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; 
v___x_2872_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__4));
v___x_2873_ = l_String_toRawSubstring_x27(v___x_2872_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock(lean_object* v_ctx_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_){
_start:
{
lean_object* v_typeInfos_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v_auxDefs_2900_; lean_object* v___x_2901_; 
v_typeInfos_2897_ = lean_ctor_get(v_ctx_2889_, 1);
v___x_2898_ = lean_array_get_size(v_typeInfos_2897_);
v___x_2899_ = lean_unsigned_to_nat(0u);
v_auxDefs_2900_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__2));
v___x_2901_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0___redArg(v___x_2898_, v_ctx_2889_, v___x_2899_, v_auxDefs_2900_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v_toCold_2902_; lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2938_; 
v_toCold_2902_ = lean_ctor_get(v_a_2894_, 0);
v_a_2903_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2905_ = v___x_2901_;
v_isShared_2906_ = v_isSharedCheck_2938_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v___x_2901_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2938_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v_ref_2907_; lean_object* v_quotContext_2908_; lean_object* v_currMacroScope_2909_; uint8_t v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2936_; 
v_ref_2907_ = lean_ctor_get(v_a_2894_, 2);
v_quotContext_2908_ = lean_ctor_get(v_toCold_2902_, 8);
v_currMacroScope_2909_ = lean_ctor_get(v_toCold_2902_, 9);
v___x_2910_ = 0;
v___x_2911_ = l_Lean_SourceInfo_fromRef(v_ref_2907_, v___x_2910_);
v___x_2912_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__0));
v___x_2913_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1));
lean_inc_n(v___x_2911_, 8);
v___x_2914_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2911_);
lean_ctor_set(v___x_2914_, 1, v___x_2912_);
v___x_2915_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_2916_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__2));
v___x_2917_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3));
v___x_2918_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2911_);
lean_ctor_set(v___x_2918_, 1, v___x_2916_);
v___x_2919_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__5, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__5_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__5);
v___x_2920_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__7));
lean_inc(v_currMacroScope_2909_);
lean_inc(v_quotContext_2908_);
v___x_2921_ = l_Lean_addMacroScope(v_quotContext_2908_, v___x_2920_, v_currMacroScope_2909_);
v___x_2922_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__10));
v___x_2923_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2911_);
lean_ctor_set(v___x_2923_, 1, v___x_2919_);
lean_ctor_set(v___x_2923_, 2, v___x_2921_);
lean_ctor_set(v___x_2923_, 3, v___x_2922_);
v___x_2924_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11);
v___x_2925_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2911_);
lean_ctor_set(v___x_2925_, 1, v___x_2915_);
lean_ctor_set(v___x_2925_, 2, v___x_2924_);
v___x_2926_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__11));
v___x_2927_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2911_);
lean_ctor_set(v___x_2927_, 1, v___x_2926_);
v___x_2928_ = l_Lean_Syntax_node4(v___x_2911_, v___x_2917_, v___x_2918_, v___x_2923_, v___x_2925_, v___x_2927_);
v___x_2929_ = l_Array_mkArray1___redArg(v___x_2928_);
v___x_2930_ = l_Array_append___redArg(v___x_2929_, v_a_2903_);
lean_dec(v_a_2903_);
v___x_2931_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2931_, 0, v___x_2911_);
lean_ctor_set(v___x_2931_, 1, v___x_2915_);
lean_ctor_set(v___x_2931_, 2, v___x_2930_);
v___x_2932_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__12));
v___x_2933_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2933_, 0, v___x_2911_);
lean_ctor_set(v___x_2933_, 1, v___x_2932_);
v___x_2934_ = l_Lean_Syntax_node3(v___x_2911_, v___x_2913_, v___x_2914_, v___x_2931_, v___x_2933_);
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 0, v___x_2934_);
v___x_2936_ = v___x_2905_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v___x_2934_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
else
{
lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2946_; 
v_a_2939_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2941_ = v___x_2901_;
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_dec(v___x_2901_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2944_; 
if (v_isShared_2942_ == 0)
{
v___x_2944_ = v___x_2941_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2939_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___boxed(lean_object* v_ctx_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock(v_ctx_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_);
lean_dec(v_a_2953_);
lean_dec_ref(v_a_2952_);
lean_dec(v_a_2951_);
lean_dec_ref(v_a_2950_);
lean_dec(v_a_2949_);
lean_dec_ref(v_a_2948_);
lean_dec_ref(v_ctx_2947_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0(lean_object* v_upperBound_2956_, lean_object* v_ctx_2957_, lean_object* v_inst_2958_, lean_object* v_R_2959_, lean_object* v_a_2960_, lean_object* v_b_2961_, lean_object* v_c_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
lean_object* v___x_2970_; 
v___x_2970_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0___redArg(v_upperBound_2956_, v_ctx_2957_, v_a_2960_, v_b_2961_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0___boxed(lean_object* v_upperBound_2971_, lean_object* v_ctx_2972_, lean_object* v_inst_2973_, lean_object* v_R_2974_, lean_object* v_a_2975_, lean_object* v_b_2976_, lean_object* v_c_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_){
_start:
{
lean_object* v_res_2985_; 
v_res_2985_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0(v_upperBound_2971_, v_ctx_2972_, v_inst_2973_, v_R_2974_, v_a_2975_, v_b_2976_, v_c_2977_, v___y_2978_, v___y_2979_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_);
lean_dec(v___y_2983_);
lean_dec_ref(v___y_2982_);
lean_dec(v___y_2981_);
lean_dec_ref(v___y_2980_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec_ref(v_ctx_2972_);
lean_dec(v_upperBound_2971_);
return v_res_2985_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2986_; double v___x_2987_; 
v___x_2986_ = lean_unsigned_to_nat(0u);
v___x_2987_ = lean_float_of_nat(v___x_2986_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg(lean_object* v_cls_2990_, lean_object* v_msg_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
lean_object* v_ref_2997_; lean_object* v___x_2998_; lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3043_; 
v_ref_2997_ = lean_ctor_get(v___y_2994_, 2);
v___x_2998_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(v_msg_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3001_ = v___x_2998_;
v_isShared_3002_ = v_isSharedCheck_3043_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2998_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3043_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3003_; lean_object* v_traceState_3004_; lean_object* v_env_3005_; lean_object* v_nextMacroScope_3006_; lean_object* v_ngen_3007_; lean_object* v_auxDeclNGen_3008_; lean_object* v_cache_3009_; lean_object* v_messages_3010_; lean_object* v_infoState_3011_; lean_object* v_snapshotTasks_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3042_; 
v___x_3003_ = lean_st_ref_take(v___y_2995_);
v_traceState_3004_ = lean_ctor_get(v___x_3003_, 4);
v_env_3005_ = lean_ctor_get(v___x_3003_, 0);
v_nextMacroScope_3006_ = lean_ctor_get(v___x_3003_, 1);
v_ngen_3007_ = lean_ctor_get(v___x_3003_, 2);
v_auxDeclNGen_3008_ = lean_ctor_get(v___x_3003_, 3);
v_cache_3009_ = lean_ctor_get(v___x_3003_, 5);
v_messages_3010_ = lean_ctor_get(v___x_3003_, 6);
v_infoState_3011_ = lean_ctor_get(v___x_3003_, 7);
v_snapshotTasks_3012_ = lean_ctor_get(v___x_3003_, 8);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3014_ = v___x_3003_;
v_isShared_3015_ = v_isSharedCheck_3042_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_snapshotTasks_3012_);
lean_inc(v_infoState_3011_);
lean_inc(v_messages_3010_);
lean_inc(v_cache_3009_);
lean_inc(v_traceState_3004_);
lean_inc(v_auxDeclNGen_3008_);
lean_inc(v_ngen_3007_);
lean_inc(v_nextMacroScope_3006_);
lean_inc(v_env_3005_);
lean_dec(v___x_3003_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3042_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
uint64_t v_tid_3016_; lean_object* v_traces_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3041_; 
v_tid_3016_ = lean_ctor_get_uint64(v_traceState_3004_, sizeof(void*)*1);
v_traces_3017_ = lean_ctor_get(v_traceState_3004_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v_traceState_3004_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3019_ = v_traceState_3004_;
v_isShared_3020_ = v_isSharedCheck_3041_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_traces_3017_);
lean_dec(v_traceState_3004_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3041_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3021_; double v___x_3022_; uint8_t v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3031_; 
v___x_3021_ = lean_box(0);
v___x_3022_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___closed__0);
v___x_3023_ = 0;
v___x_3024_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__22));
v___x_3025_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3025_, 0, v_cls_2990_);
lean_ctor_set(v___x_3025_, 1, v___x_3021_);
lean_ctor_set(v___x_3025_, 2, v___x_3024_);
lean_ctor_set_float(v___x_3025_, sizeof(void*)*3, v___x_3022_);
lean_ctor_set_float(v___x_3025_, sizeof(void*)*3 + 8, v___x_3022_);
lean_ctor_set_uint8(v___x_3025_, sizeof(void*)*3 + 16, v___x_3023_);
v___x_3026_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___closed__1));
v___x_3027_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3025_);
lean_ctor_set(v___x_3027_, 1, v_a_2999_);
lean_ctor_set(v___x_3027_, 2, v___x_3026_);
lean_inc(v_ref_2997_);
v___x_3028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3028_, 0, v_ref_2997_);
lean_ctor_set(v___x_3028_, 1, v___x_3027_);
v___x_3029_ = l_Lean_PersistentArray_push___redArg(v_traces_3017_, v___x_3028_);
if (v_isShared_3020_ == 0)
{
lean_ctor_set(v___x_3019_, 0, v___x_3029_);
v___x_3031_ = v___x_3019_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v___x_3029_);
lean_ctor_set_uint64(v_reuseFailAlloc_3040_, sizeof(void*)*1, v_tid_3016_);
v___x_3031_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
lean_object* v___x_3033_; 
if (v_isShared_3015_ == 0)
{
lean_ctor_set(v___x_3014_, 4, v___x_3031_);
v___x_3033_ = v___x_3014_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_env_3005_);
lean_ctor_set(v_reuseFailAlloc_3039_, 1, v_nextMacroScope_3006_);
lean_ctor_set(v_reuseFailAlloc_3039_, 2, v_ngen_3007_);
lean_ctor_set(v_reuseFailAlloc_3039_, 3, v_auxDeclNGen_3008_);
lean_ctor_set(v_reuseFailAlloc_3039_, 4, v___x_3031_);
lean_ctor_set(v_reuseFailAlloc_3039_, 5, v_cache_3009_);
lean_ctor_set(v_reuseFailAlloc_3039_, 6, v_messages_3010_);
lean_ctor_set(v_reuseFailAlloc_3039_, 7, v_infoState_3011_);
lean_ctor_set(v_reuseFailAlloc_3039_, 8, v_snapshotTasks_3012_);
v___x_3033_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3037_; 
v___x_3034_ = lean_st_ref_put(v___y_2995_, v___x_3033_);
v___x_3035_ = lean_box(0);
if (v_isShared_3002_ == 0)
{
lean_ctor_set(v___x_3001_, 0, v___x_3035_);
v___x_3037_ = v___x_3001_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3035_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___boxed(lean_object* v_cls_3044_, lean_object* v_msg_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_){
_start:
{
lean_object* v_res_3051_; 
v_res_3051_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg(v_cls_3044_, v_msg_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
return v_res_3051_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__0(lean_object* v_a_3052_, lean_object* v_a_3053_){
_start:
{
if (lean_obj_tag(v_a_3052_) == 0)
{
lean_object* v___x_3054_; 
v___x_3054_ = l_List_reverse___redArg(v_a_3053_);
return v___x_3054_;
}
else
{
lean_object* v_head_3055_; lean_object* v_tail_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3065_; 
v_head_3055_ = lean_ctor_get(v_a_3052_, 0);
v_tail_3056_ = lean_ctor_get(v_a_3052_, 1);
v_isSharedCheck_3065_ = !lean_is_exclusive(v_a_3052_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3058_ = v_a_3052_;
v_isShared_3059_ = v_isSharedCheck_3065_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_tail_3056_);
lean_inc(v_head_3055_);
lean_dec(v_a_3052_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3065_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3060_; lean_object* v___x_3062_; 
v___x_3060_ = l_Lean_MessageData_ofSyntax(v_head_3055_);
if (v_isShared_3059_ == 0)
{
lean_ctor_set(v___x_3058_, 1, v_a_3053_);
lean_ctor_set(v___x_3058_, 0, v___x_3060_);
v___x_3062_ = v___x_3058_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3060_);
lean_ctor_set(v_reuseFailAlloc_3064_, 1, v_a_3053_);
v___x_3062_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
v_a_3052_ = v_tail_3056_;
v_a_3053_ = v___x_3062_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3(void){
_start:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3073_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__0));
v___x_3074_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__2));
v___x_3075_ = l_Lean_Name_append(v___x_3074_, v___x_3073_);
return v___x_3075_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5(void){
_start:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3077_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__4));
v___x_3078_ = l_Lean_stringToMessageData(v___x_3077_);
return v___x_3078_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__17(void){
_start:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3106_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__16));
v___x_3107_ = l_String_toRawSubstring_x27(v___x_3106_);
return v___x_3107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds(lean_object* v_declName_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v_cmds_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v_options_3126_; lean_object* v_inheritedTraceOptions_3127_; lean_object* v___y_3128_; uint8_t v___x_3158_; lean_object* v___x_3159_; 
v___x_3119_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader___closed__0));
v___x_3120_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__1_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_));
v___x_3158_ = 0;
lean_inc(v_declName_3111_);
v___x_3159_ = l_Lean_Elab_Deriving_mkContext(v___x_3119_, v___x_3120_, v_declName_3111_, v___x_3158_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_a_3160_; lean_object* v___x_3161_; 
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
lean_inc(v_a_3160_);
lean_dec_ref_known(v___x_3159_, 1);
v___x_3161_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock(v_a_3160_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_object* v_a_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; uint8_t v___x_3166_; lean_object* v___x_3167_; 
v_a_3162_ = lean_ctor_get(v___x_3161_, 0);
lean_inc(v_a_3162_);
lean_dec_ref_known(v___x_3161_, 1);
v___x_3163_ = lean_unsigned_to_nat(1u);
v___x_3164_ = lean_mk_empty_array_with_capacity(v___x_3163_);
lean_inc_ref(v___x_3164_);
v___x_3165_ = lean_array_push(v___x_3164_, v_declName_3111_);
v___x_3166_ = 1;
lean_inc(v_a_3160_);
v___x_3167_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_a_3160_, v___x_3119_, v___x_3165_, v___x_3166_, v_a_3112_, v_a_3113_, v_a_3114_, v_a_3115_, v_a_3116_, v_a_3117_);
lean_dec_ref(v___x_3165_);
if (lean_obj_tag(v___x_3167_) == 0)
{
lean_object* v_a_3168_; lean_object* v_instName_3169_; uint8_t v_usePartial_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
v_a_3168_ = lean_ctor_get(v___x_3167_, 0);
lean_inc(v_a_3168_);
lean_dec_ref_known(v___x_3167_, 1);
v_instName_3169_ = lean_ctor_get(v_a_3160_, 0);
lean_inc(v_instName_3169_);
v_usePartial_3170_ = lean_ctor_get_uint8(v_a_3160_, sizeof(void*)*3);
lean_dec(v_a_3160_);
v___x_3171_ = lean_array_push(v___x_3164_, v_a_3162_);
v___x_3172_ = l_Array_append___redArg(v___x_3171_, v_a_3168_);
lean_dec(v_a_3168_);
if (v_usePartial_3170_ == 0)
{
lean_object* v_toCold_3173_; lean_object* v_ref_3174_; lean_object* v_options_3175_; lean_object* v_quotContext_3176_; lean_object* v_currMacroScope_3177_; lean_object* v_inheritedTraceOptions_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
v_toCold_3173_ = lean_ctor_get(v_a_3116_, 0);
v_ref_3174_ = lean_ctor_get(v_a_3116_, 2);
v_options_3175_ = lean_ctor_get(v_toCold_3173_, 2);
v_quotContext_3176_ = lean_ctor_get(v_toCold_3173_, 8);
v_currMacroScope_3177_ = lean_ctor_get(v_toCold_3173_, 9);
v_inheritedTraceOptions_3178_ = lean_ctor_get(v_toCold_3173_, 11);
v___x_3179_ = l_Lean_SourceInfo_fromRef(v_ref_3174_, v_usePartial_3170_);
v___x_3180_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__6));
v___x_3181_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__7));
lean_inc_n(v___x_3179_, 10);
v___x_3182_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3182_, 0, v___x_3179_);
lean_ctor_set(v___x_3182_, 1, v___x_3180_);
v___x_3183_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__8));
v___x_3184_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3179_);
lean_ctor_set(v___x_3184_, 1, v___x_3183_);
v___x_3185_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_3186_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__10));
v___x_3187_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__12));
v___x_3188_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11);
v___x_3189_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3179_);
lean_ctor_set(v___x_3189_, 1, v___x_3185_);
lean_ctor_set(v___x_3189_, 2, v___x_3188_);
lean_inc_ref(v___x_3189_);
v___x_3190_ = l_Lean_Syntax_node1(v___x_3179_, v___x_3187_, v___x_3189_);
v___x_3191_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__15));
v___x_3192_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__17, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__17_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__17);
v___x_3193_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__18));
lean_inc(v_currMacroScope_3177_);
lean_inc(v_quotContext_3176_);
v___x_3194_ = l_Lean_addMacroScope(v_quotContext_3176_, v___x_3193_, v_currMacroScope_3177_);
v___x_3195_ = lean_box(0);
v___x_3196_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3179_);
lean_ctor_set(v___x_3196_, 1, v___x_3192_);
lean_ctor_set(v___x_3196_, 2, v___x_3194_);
lean_ctor_set(v___x_3196_, 3, v___x_3195_);
v___x_3197_ = l_Lean_Syntax_node2(v___x_3179_, v___x_3191_, v___x_3196_, v___x_3189_);
v___x_3198_ = l_Lean_Syntax_node2(v___x_3179_, v___x_3186_, v___x_3190_, v___x_3197_);
v___x_3199_ = l_Lean_Syntax_node1(v___x_3179_, v___x_3185_, v___x_3198_);
v___x_3200_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__19));
v___x_3201_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3179_);
lean_ctor_set(v___x_3201_, 1, v___x_3200_);
v___x_3202_ = l_Lean_mkIdent(v_instName_3169_);
v___x_3203_ = l_Lean_Syntax_node1(v___x_3179_, v___x_3185_, v___x_3202_);
v___x_3204_ = l_Lean_Syntax_node5(v___x_3179_, v___x_3181_, v___x_3182_, v___x_3184_, v___x_3199_, v___x_3201_, v___x_3203_);
v___x_3205_ = lean_array_push(v___x_3172_, v___x_3204_);
lean_inc_ref(v_inheritedTraceOptions_3178_);
lean_inc_ref(v_options_3175_);
v_cmds_3122_ = v___x_3205_;
v___y_3123_ = v_a_3114_;
v___y_3124_ = v_a_3115_;
v___y_3125_ = v_a_3116_;
v_options_3126_ = v_options_3175_;
v_inheritedTraceOptions_3127_ = v_inheritedTraceOptions_3178_;
v___y_3128_ = v_a_3117_;
goto v___jp_3121_;
}
else
{
lean_object* v_toCold_3206_; lean_object* v_options_3207_; lean_object* v_inheritedTraceOptions_3208_; 
lean_dec(v_instName_3169_);
v_toCold_3206_ = lean_ctor_get(v_a_3116_, 0);
v_options_3207_ = lean_ctor_get(v_toCold_3206_, 2);
v_inheritedTraceOptions_3208_ = lean_ctor_get(v_toCold_3206_, 11);
lean_inc_ref(v_inheritedTraceOptions_3208_);
lean_inc_ref(v_options_3207_);
v_cmds_3122_ = v___x_3172_;
v___y_3123_ = v_a_3114_;
v___y_3124_ = v_a_3115_;
v___y_3125_ = v_a_3116_;
v_options_3126_ = v_options_3207_;
v_inheritedTraceOptions_3127_ = v_inheritedTraceOptions_3208_;
v___y_3128_ = v_a_3117_;
goto v___jp_3121_;
}
}
else
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3216_; 
lean_dec_ref(v___x_3164_);
lean_dec(v_a_3162_);
lean_dec(v_a_3160_);
v_a_3209_ = lean_ctor_get(v___x_3167_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3211_ = v___x_3167_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3167_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3214_; 
if (v_isShared_3212_ == 0)
{
v___x_3214_ = v___x_3211_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3209_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
else
{
lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3224_; 
lean_dec(v_a_3160_);
lean_dec(v_declName_3111_);
v_a_3217_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3219_ = v___x_3161_;
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3161_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3222_; 
if (v_isShared_3220_ == 0)
{
v___x_3222_ = v___x_3219_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_a_3217_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
}
else
{
lean_object* v_a_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3232_; 
lean_dec(v_declName_3111_);
v_a_3225_ = lean_ctor_get(v___x_3159_, 0);
v_isSharedCheck_3232_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3232_ == 0)
{
v___x_3227_ = v___x_3159_;
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_dec(v___x_3159_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3230_; 
if (v_isShared_3228_ == 0)
{
v___x_3230_ = v___x_3227_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_a_3225_);
v___x_3230_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
return v___x_3230_;
}
}
}
v___jp_3121_:
{
uint8_t v_hasTrace_3129_; 
v_hasTrace_3129_ = lean_ctor_get_uint8(v_options_3126_, sizeof(void*)*1);
if (v_hasTrace_3129_ == 0)
{
lean_object* v___x_3130_; 
lean_dec_ref(v_inheritedTraceOptions_3127_);
lean_dec_ref(v_options_3126_);
v___x_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3130_, 0, v_cmds_3122_);
return v___x_3130_;
}
else
{
lean_object* v___x_3131_; lean_object* v___x_3132_; uint8_t v___x_3133_; 
v___x_3131_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__0));
v___x_3132_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3);
v___x_3133_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3127_, v_options_3126_, v___x_3132_);
lean_dec_ref(v_options_3126_);
lean_dec_ref(v_inheritedTraceOptions_3127_);
if (v___x_3133_ == 0)
{
lean_object* v___x_3134_; 
v___x_3134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3134_, 0, v_cmds_3122_);
return v___x_3134_;
}
else
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3135_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5);
lean_inc_ref(v_cmds_3122_);
v___x_3136_ = lean_array_to_list(v_cmds_3122_);
v___x_3137_ = lean_box(0);
v___x_3138_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__0(v___x_3136_, v___x_3137_);
v___x_3139_ = l_Lean_MessageData_ofList(v___x_3138_);
v___x_3140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3135_);
lean_ctor_set(v___x_3140_, 1, v___x_3139_);
v___x_3141_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg(v___x_3131_, v___x_3140_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3128_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3148_ == 0)
{
lean_object* v_unused_3149_; 
v_unused_3149_ = lean_ctor_get(v___x_3141_, 0);
lean_dec(v_unused_3149_);
v___x_3143_ = v___x_3141_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_dec(v___x_3141_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
lean_ctor_set(v___x_3143_, 0, v_cmds_3122_);
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_cmds_3122_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
else
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
lean_dec_ref(v_cmds_3122_);
v_a_3150_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3141_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3141_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___boxed(lean_object* v_declName_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_){
_start:
{
lean_object* v_res_3241_; 
v_res_3241_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds(v_declName_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_);
lean_dec(v_a_3239_);
lean_dec_ref(v_a_3238_);
lean_dec(v_a_3237_);
lean_dec_ref(v_a_3236_);
lean_dec(v_a_3235_);
lean_dec_ref(v_a_3234_);
return v_res_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1(lean_object* v_cls_3242_, lean_object* v_msg_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_){
_start:
{
lean_object* v___x_3251_; 
v___x_3251_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg(v_cls_3242_, v_msg_3243_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___boxed(lean_object* v_cls_3252_, lean_object* v_msg_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_){
_start:
{
lean_object* v_res_3261_; 
v_res_3261_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1(v_cls_3252_, v_msg_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
lean_dec(v___y_3259_);
lean_dec_ref(v___y_3258_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
return v_res_3261_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__3(void){
_start:
{
lean_object* v___x_3269_; lean_object* v___x_3270_; 
v___x_3269_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__2));
v___x_3270_ = l_String_toRawSubstring_x27(v___x_3269_);
return v___x_3270_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__6(void){
_start:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3274_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__5));
v___x_3275_ = l_String_toRawSubstring_x27(v___x_3274_);
return v___x_3275_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__12(void){
_start:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3288_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__11));
v___x_3289_ = l_String_toRawSubstring_x27(v___x_3288_);
return v___x_3289_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__16(void){
_start:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3295_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__15));
v___x_3296_ = l_String_toRawSubstring_x27(v___x_3295_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg(lean_object* v_ctx_3300_, lean_object* v_name_3301_, lean_object* v_a_3302_){
_start:
{
lean_object* v_toCold_3304_; lean_object* v_auxFunNames_3305_; lean_object* v_ref_3306_; lean_object* v_quotContext_3307_; lean_object* v_currMacroScope_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v_auxFunName_3311_; uint8_t v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
v_toCold_3304_ = lean_ctor_get(v_a_3302_, 0);
v_auxFunNames_3305_ = lean_ctor_get(v_ctx_3300_, 2);
v_ref_3306_ = lean_ctor_get(v_a_3302_, 2);
v_quotContext_3307_ = lean_ctor_get(v_toCold_3304_, 8);
v_currMacroScope_3308_ = lean_ctor_get(v_toCold_3304_, 9);
v___x_3309_ = lean_box(0);
v___x_3310_ = lean_unsigned_to_nat(0u);
v_auxFunName_3311_ = lean_array_get_borrowed(v___x_3309_, v_auxFunNames_3305_, v___x_3310_);
v___x_3312_ = 0;
v___x_3313_ = l_Lean_SourceInfo_fromRef(v_ref_3306_, v___x_3312_);
v___x_3314_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__2));
v___x_3315_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__4));
v___x_3316_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_3317_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11);
lean_inc_n(v___x_3313_, 26);
v___x_3318_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3313_);
lean_ctor_set(v___x_3318_, 1, v___x_3316_);
lean_ctor_set(v___x_3318_, 2, v___x_3317_);
lean_inc_ref_n(v___x_3318_, 12);
v___x_3319_ = l_Lean_Syntax_node7(v___x_3313_, v___x_3315_, v___x_3318_, v___x_3318_, v___x_3318_, v___x_3318_, v___x_3318_, v___x_3318_, v___x_3318_);
v___x_3320_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__6));
v___x_3321_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__7));
v___x_3322_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3313_);
lean_ctor_set(v___x_3322_, 1, v___x_3321_);
v___x_3323_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__9));
lean_inc(v_auxFunName_3311_);
v___x_3324_ = l_Lean_mkIdent(v_auxFunName_3311_);
v___x_3325_ = l_Lean_Syntax_node2(v___x_3313_, v___x_3323_, v___x_3324_, v___x_3318_);
v___x_3326_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__11));
v___x_3327_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__1));
v___x_3328_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__19));
v___x_3329_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3313_);
lean_ctor_set(v___x_3329_, 1, v___x_3328_);
v___x_3330_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__3, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__3_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__3);
v___x_3331_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__4));
lean_inc_n(v_currMacroScope_3308_, 6);
lean_inc_n(v_quotContext_3307_, 6);
v___x_3332_ = l_Lean_addMacroScope(v_quotContext_3307_, v___x_3331_, v_currMacroScope_3308_);
v___x_3333_ = lean_box(0);
v___x_3334_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3313_);
lean_ctor_set(v___x_3334_, 1, v___x_3330_);
lean_ctor_set(v___x_3334_, 2, v___x_3332_);
lean_ctor_set(v___x_3334_, 3, v___x_3333_);
v___x_3335_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__6, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__6_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__6);
v___x_3336_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__7));
v___x_3337_ = l_Lean_addMacroScope(v_quotContext_3307_, v___x_3336_, v_currMacroScope_3308_);
v___x_3338_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3313_);
lean_ctor_set(v___x_3338_, 1, v___x_3335_);
lean_ctor_set(v___x_3338_, 2, v___x_3337_);
lean_ctor_set(v___x_3338_, 3, v___x_3333_);
v___x_3339_ = l_Lean_Syntax_node2(v___x_3313_, v___x_3316_, v___x_3334_, v___x_3338_);
v___x_3340_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__11));
v___x_3341_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3313_);
lean_ctor_set(v___x_3341_, 1, v___x_3340_);
v___x_3342_ = l_Lean_mkCIdent(v_name_3301_);
lean_inc_ref(v___x_3341_);
v___x_3343_ = l_Lean_Syntax_node2(v___x_3313_, v___x_3316_, v___x_3341_, v___x_3342_);
v___x_3344_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__40));
v___x_3345_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3313_);
lean_ctor_set(v___x_3345_, 1, v___x_3344_);
v___x_3346_ = l_Lean_Syntax_node5(v___x_3313_, v___x_3327_, v___x_3329_, v___x_3339_, v___x_3343_, v___x_3318_, v___x_3345_);
v___x_3347_ = l_Lean_Syntax_node1(v___x_3313_, v___x_3316_, v___x_3346_);
v___x_3348_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__13));
v___x_3349_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14);
v___x_3350_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__15));
v___x_3351_ = l_Lean_addMacroScope(v_quotContext_3307_, v___x_3350_, v_currMacroScope_3308_);
v___x_3352_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__10));
v___x_3353_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3313_);
lean_ctor_set(v___x_3353_, 1, v___x_3349_);
lean_ctor_set(v___x_3353_, 2, v___x_3351_);
lean_ctor_set(v___x_3353_, 3, v___x_3352_);
v___x_3354_ = l_Lean_Syntax_node2(v___x_3313_, v___x_3348_, v___x_3341_, v___x_3353_);
v___x_3355_ = l_Lean_Syntax_node1(v___x_3313_, v___x_3316_, v___x_3354_);
v___x_3356_ = l_Lean_Syntax_node2(v___x_3313_, v___x_3326_, v___x_3347_, v___x_3355_);
v___x_3357_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__21));
v___x_3358_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__22));
v___x_3359_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3313_);
lean_ctor_set(v___x_3359_, 1, v___x_3358_);
v___x_3360_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3));
v___x_3361_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35);
v___x_3362_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__36));
v___x_3363_ = l_Lean_addMacroScope(v_quotContext_3307_, v___x_3362_, v_currMacroScope_3308_);
v___x_3364_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__13));
v___x_3365_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3313_);
lean_ctor_set(v___x_3365_, 1, v___x_3361_);
lean_ctor_set(v___x_3365_, 2, v___x_3363_);
lean_ctor_set(v___x_3365_, 3, v___x_3364_);
v___x_3366_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__12, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__12_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__12);
v___x_3367_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__14));
v___x_3368_ = l_Lean_addMacroScope(v_quotContext_3307_, v___x_3367_, v_currMacroScope_3308_);
v___x_3369_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3313_);
lean_ctor_set(v___x_3369_, 1, v___x_3366_);
lean_ctor_set(v___x_3369_, 2, v___x_3368_);
lean_ctor_set(v___x_3369_, 3, v___x_3333_);
v___x_3370_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__16, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__16_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__16);
v___x_3371_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__17));
v___x_3372_ = l_Lean_addMacroScope(v_quotContext_3307_, v___x_3371_, v_currMacroScope_3308_);
v___x_3373_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3313_);
lean_ctor_set(v___x_3373_, 1, v___x_3370_);
lean_ctor_set(v___x_3373_, 2, v___x_3372_);
lean_ctor_set(v___x_3373_, 3, v___x_3333_);
v___x_3374_ = l_Lean_Syntax_node2(v___x_3313_, v___x_3316_, v___x_3369_, v___x_3373_);
v___x_3375_ = l_Lean_Syntax_node2(v___x_3313_, v___x_3360_, v___x_3365_, v___x_3374_);
v___x_3376_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__25));
v___x_3377_ = l_Lean_Syntax_node2(v___x_3313_, v___x_3376_, v___x_3318_, v___x_3318_);
v___x_3378_ = l_Lean_Syntax_node4(v___x_3313_, v___x_3357_, v___x_3359_, v___x_3375_, v___x_3377_, v___x_3318_);
v___x_3379_ = l_Lean_Syntax_node5(v___x_3313_, v___x_3320_, v___x_3322_, v___x_3325_, v___x_3356_, v___x_3378_, v___x_3318_);
v___x_3380_ = l_Lean_Syntax_node2(v___x_3313_, v___x_3314_, v___x_3319_, v___x_3379_);
v___x_3381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3380_);
return v___x_3381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___boxed(lean_object* v_ctx_3382_, lean_object* v_name_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_){
_start:
{
lean_object* v_res_3386_; 
v_res_3386_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg(v_ctx_3382_, v_name_3383_, v_a_3384_);
lean_dec_ref(v_a_3384_);
lean_dec_ref(v_ctx_3382_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun(lean_object* v_ctx_3387_, lean_object* v_name_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_){
_start:
{
lean_object* v___x_3396_; 
v___x_3396_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg(v_ctx_3387_, v_name_3388_, v_a_3393_);
return v___x_3396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___boxed(lean_object* v_ctx_3397_, lean_object* v_name_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_){
_start:
{
lean_object* v_res_3406_; 
v_res_3406_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun(v_ctx_3397_, v_name_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
lean_dec(v_a_3404_);
lean_dec_ref(v_a_3403_);
lean_dec(v_a_3402_);
lean_dec_ref(v_a_3401_);
lean_dec(v_a_3400_);
lean_dec_ref(v_a_3399_);
lean_dec_ref(v_ctx_3397_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumCmd(lean_object* v_name_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_){
_start:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; uint8_t v___x_3417_; lean_object* v___x_3418_; 
v___x_3415_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader___closed__0));
v___x_3416_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__1_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_));
v___x_3417_ = 1;
lean_inc(v_name_3407_);
v___x_3418_ = l_Lean_Elab_Deriving_mkContext(v___x_3415_, v___x_3416_, v_name_3407_, v___x_3417_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; lean_object* v___x_3420_; lean_object* v_a_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
lean_inc(v_a_3419_);
lean_dec_ref_known(v___x_3418_, 1);
lean_inc(v_name_3407_);
v___x_3420_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg(v_a_3419_, v_name_3407_, v_a_3412_);
v_a_3421_ = lean_ctor_get(v___x_3420_, 0);
lean_inc(v_a_3421_);
lean_dec_ref(v___x_3420_);
v___x_3422_ = lean_unsigned_to_nat(1u);
v___x_3423_ = lean_mk_empty_array_with_capacity(v___x_3422_);
lean_inc_ref(v___x_3423_);
v___x_3424_ = lean_array_push(v___x_3423_, v_name_3407_);
v___x_3425_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_a_3419_, v___x_3415_, v___x_3424_, v___x_3417_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
lean_dec_ref(v___x_3424_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_toCold_3426_; lean_object* v_options_3427_; lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3468_; 
v_toCold_3426_ = lean_ctor_get(v_a_3412_, 0);
v_options_3427_ = lean_ctor_get(v_toCold_3426_, 2);
v_a_3428_ = lean_ctor_get(v___x_3425_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3430_ = v___x_3425_;
v_isShared_3431_ = v_isSharedCheck_3468_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_a_3428_);
lean_dec(v___x_3425_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3468_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v_inheritedTraceOptions_3432_; uint8_t v_hasTrace_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v_inheritedTraceOptions_3432_ = lean_ctor_get(v_toCold_3426_, 11);
v_hasTrace_3433_ = lean_ctor_get_uint8(v_options_3427_, sizeof(void*)*1);
v___x_3434_ = lean_array_push(v___x_3423_, v_a_3421_);
v___x_3435_ = l_Array_append___redArg(v___x_3434_, v_a_3428_);
lean_dec(v_a_3428_);
if (v_hasTrace_3433_ == 0)
{
lean_object* v___x_3437_; 
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 0, v___x_3435_);
v___x_3437_ = v___x_3430_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v___x_3435_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
else
{
lean_object* v___x_3439_; lean_object* v___x_3440_; uint8_t v___x_3441_; 
v___x_3439_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__0));
v___x_3440_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3);
v___x_3441_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3432_, v_options_3427_, v___x_3440_);
if (v___x_3441_ == 0)
{
lean_object* v___x_3443_; 
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 0, v___x_3435_);
v___x_3443_ = v___x_3430_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3435_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
else
{
lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; 
lean_del_object(v___x_3430_);
v___x_3445_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5);
lean_inc_ref(v___x_3435_);
v___x_3446_ = lean_array_to_list(v___x_3435_);
v___x_3447_ = lean_box(0);
v___x_3448_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__0(v___x_3446_, v___x_3447_);
v___x_3449_ = l_Lean_MessageData_ofList(v___x_3448_);
v___x_3450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3445_);
lean_ctor_set(v___x_3450_, 1, v___x_3449_);
v___x_3451_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg(v___x_3439_, v___x_3450_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3458_; 
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3458_ == 0)
{
lean_object* v_unused_3459_; 
v_unused_3459_ = lean_ctor_get(v___x_3451_, 0);
lean_dec(v_unused_3459_);
v___x_3453_ = v___x_3451_;
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
else
{
lean_dec(v___x_3451_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3456_; 
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 0, v___x_3435_);
v___x_3456_ = v___x_3453_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v___x_3435_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
else
{
lean_object* v_a_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3467_; 
lean_dec_ref(v___x_3435_);
v_a_3460_ = lean_ctor_get(v___x_3451_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3462_ = v___x_3451_;
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_a_3460_);
lean_dec(v___x_3451_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3465_; 
if (v_isShared_3463_ == 0)
{
v___x_3465_ = v___x_3462_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_a_3460_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3476_; 
lean_dec_ref(v___x_3423_);
lean_dec(v_a_3421_);
v_a_3469_ = lean_ctor_get(v___x_3425_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3471_ = v___x_3425_;
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3425_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3474_; 
if (v_isShared_3472_ == 0)
{
v___x_3474_ = v___x_3471_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_a_3469_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
}
}
else
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3484_; 
lean_dec(v_name_3407_);
v_a_3477_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3479_ = v___x_3418_;
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___x_3418_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3482_; 
if (v_isShared_3480_ == 0)
{
v___x_3482_ = v___x_3479_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_a_3477_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumCmd___boxed(lean_object* v_name_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_){
_start:
{
lean_object* v_res_3493_; 
v_res_3493_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumCmd(v_name_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_);
lean_dec(v_a_3491_);
lean_dec_ref(v_a_3490_);
lean_dec(v_a_3489_);
lean_dec_ref(v_a_3488_);
lean_dec(v_a_3487_);
lean_dec_ref(v_a_3486_);
return v_res_3493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__0(uint8_t v_a_3494_, lean_object* v_declName_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_){
_start:
{
if (v_a_3494_ == 0)
{
lean_object* v___x_3503_; 
v___x_3503_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds(v_declName_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_);
return v___x_3503_;
}
else
{
lean_object* v___x_3504_; 
v___x_3504_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumCmd(v_declName_3495_, v___y_3496_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_, v___y_3501_);
return v___x_3504_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__0___boxed(lean_object* v_a_3505_, lean_object* v_declName_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
uint8_t v_a_3783__boxed_3514_; lean_object* v_res_3515_; 
v_a_3783__boxed_3514_ = lean_unbox(v_a_3505_);
v_res_3515_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__0(v_a_3783__boxed_3514_, v_declName_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
return v_res_3515_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_3516_; 
v___x_3516_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3516_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3517_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__0);
v___x_3518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3517_);
return v___x_3518_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3519_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1);
v___x_3520_ = lean_unsigned_to_nat(0u);
v___x_3521_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3520_);
lean_ctor_set(v___x_3521_, 1, v___x_3520_);
lean_ctor_set(v___x_3521_, 2, v___x_3520_);
lean_ctor_set(v___x_3521_, 3, v___x_3520_);
lean_ctor_set(v___x_3521_, 4, v___x_3519_);
lean_ctor_set(v___x_3521_, 5, v___x_3519_);
lean_ctor_set(v___x_3521_, 6, v___x_3519_);
lean_ctor_set(v___x_3521_, 7, v___x_3519_);
lean_ctor_set(v___x_3521_, 8, v___x_3519_);
lean_ctor_set(v___x_3521_, 9, v___x_3519_);
lean_ctor_set(v___x_3521_, 10, v___x_3519_);
return v___x_3521_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3522_ = lean_unsigned_to_nat(32u);
v___x_3523_ = lean_mk_empty_array_with_capacity(v___x_3522_);
v___x_3524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3523_);
return v___x_3524_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3525_ = ((size_t)5ULL);
v___x_3526_ = lean_unsigned_to_nat(0u);
v___x_3527_ = lean_unsigned_to_nat(32u);
v___x_3528_ = lean_mk_empty_array_with_capacity(v___x_3527_);
v___x_3529_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__3);
v___x_3530_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3530_, 0, v___x_3529_);
lean_ctor_set(v___x_3530_, 1, v___x_3528_);
lean_ctor_set(v___x_3530_, 2, v___x_3526_);
lean_ctor_set(v___x_3530_, 3, v___x_3526_);
lean_ctor_set_usize(v___x_3530_, 4, v___x_3525_);
return v___x_3530_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3531_ = lean_box(1);
v___x_3532_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__4);
v___x_3533_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1);
v___x_3534_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3533_);
lean_ctor_set(v___x_3534_, 1, v___x_3532_);
lean_ctor_set(v___x_3534_, 2, v___x_3531_);
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(lean_object* v_msgData_3535_, lean_object* v___y_3536_){
_start:
{
lean_object* v___x_3538_; lean_object* v_env_3539_; lean_object* v___x_3540_; lean_object* v_scopes_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v_opts_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3538_ = lean_st_ref_get(v___y_3536_);
v_env_3539_ = lean_ctor_get(v___x_3538_, 0);
lean_inc_ref(v_env_3539_);
lean_dec(v___x_3538_);
v___x_3540_ = lean_st_ref_get(v___y_3536_);
v_scopes_3541_ = lean_ctor_get(v___x_3540_, 2);
lean_inc(v_scopes_3541_);
lean_dec(v___x_3540_);
v___x_3542_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3543_ = l_List_head_x21___redArg(v___x_3542_, v_scopes_3541_);
lean_dec(v_scopes_3541_);
v_opts_3544_ = lean_ctor_get(v___x_3543_, 1);
lean_inc_ref(v_opts_3544_);
lean_dec(v___x_3543_);
v___x_3545_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2);
v___x_3546_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5);
v___x_3547_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3547_, 0, v_env_3539_);
lean_ctor_set(v___x_3547_, 1, v___x_3545_);
lean_ctor_set(v___x_3547_, 2, v___x_3546_);
lean_ctor_set(v___x_3547_, 3, v_opts_3544_);
v___x_3548_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3547_);
lean_ctor_set(v___x_3548_, 1, v_msgData_3535_);
v___x_3549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3548_);
return v___x_3549_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___boxed(lean_object* v_msgData_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_msgData_3550_, v___y_3551_);
lean_dec(v___y_3551_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11___redArg(lean_object* v_msgData_3554_, lean_object* v_macroStack_3555_, lean_object* v___y_3556_){
_start:
{
lean_object* v___x_3558_; lean_object* v_scopes_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v_opts_3562_; lean_object* v___x_3563_; uint8_t v___x_3564_; 
v___x_3558_ = lean_st_ref_get(v___y_3556_);
v_scopes_3559_ = lean_ctor_get(v___x_3558_, 2);
lean_inc(v_scopes_3559_);
lean_dec(v___x_3558_);
v___x_3560_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3561_ = l_List_head_x21___redArg(v___x_3560_, v_scopes_3559_);
lean_dec(v_scopes_3559_);
v_opts_3562_ = lean_ctor_get(v___x_3561_, 1);
lean_inc_ref(v_opts_3562_);
lean_dec(v___x_3561_);
v___x_3563_ = l_Lean_Elab_pp_macroStack;
v___x_3564_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(v_opts_3562_, v___x_3563_);
lean_dec_ref(v_opts_3562_);
if (v___x_3564_ == 0)
{
lean_object* v___x_3565_; 
lean_dec(v_macroStack_3555_);
v___x_3565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3565_, 0, v_msgData_3554_);
return v___x_3565_;
}
else
{
if (lean_obj_tag(v_macroStack_3555_) == 0)
{
lean_object* v___x_3566_; 
v___x_3566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3566_, 0, v_msgData_3554_);
return v___x_3566_;
}
else
{
lean_object* v_head_3567_; lean_object* v_after_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3583_; 
v_head_3567_ = lean_ctor_get(v_macroStack_3555_, 0);
lean_inc(v_head_3567_);
v_after_3568_ = lean_ctor_get(v_head_3567_, 1);
v_isSharedCheck_3583_ = !lean_is_exclusive(v_head_3567_);
if (v_isSharedCheck_3583_ == 0)
{
lean_object* v_unused_3584_; 
v_unused_3584_ = lean_ctor_get(v_head_3567_, 0);
lean_dec(v_unused_3584_);
v___x_3570_ = v_head_3567_;
v_isShared_3571_ = v_isSharedCheck_3583_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_after_3568_);
lean_dec(v_head_3567_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3583_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3572_; lean_object* v___x_3574_; 
v___x_3572_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0);
if (v_isShared_3571_ == 0)
{
lean_ctor_set_tag(v___x_3570_, 7);
lean_ctor_set(v___x_3570_, 1, v___x_3572_);
lean_ctor_set(v___x_3570_, 0, v_msgData_3554_);
v___x_3574_ = v___x_3570_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_msgData_3554_);
lean_ctor_set(v_reuseFailAlloc_3582_, 1, v___x_3572_);
v___x_3574_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v_msgData_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3575_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_3576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3574_);
lean_ctor_set(v___x_3576_, 1, v___x_3575_);
v___x_3577_ = l_Lean_MessageData_ofSyntax(v_after_3568_);
v___x_3578_ = l_Lean_indentD(v___x_3577_);
v_msgData_3579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_3579_, 0, v___x_3576_);
lean_ctor_set(v_msgData_3579_, 1, v___x_3578_);
v___x_3580_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12(v_msgData_3579_, v_macroStack_3555_);
v___x_3581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3580_);
return v___x_3581_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_msgData_3585_, lean_object* v_macroStack_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_){
_start:
{
lean_object* v_res_3589_; 
v_res_3589_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11___redArg(v_msgData_3585_, v_macroStack_3586_, v___y_3587_);
lean_dec(v___y_3587_);
return v_res_3589_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9___redArg(lean_object* v_msg_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_){
_start:
{
lean_object* v___x_3594_; 
v___x_3594_ = l_Lean_Elab_Command_getRef___redArg(v___y_3591_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v_a_3595_; lean_object* v_macroStack_3596_; lean_object* v___x_3597_; lean_object* v_a_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v_a_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3609_; 
v_a_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc(v_a_3595_);
lean_dec_ref_known(v___x_3594_, 1);
v_macroStack_3596_ = lean_ctor_get(v___y_3591_, 4);
v___x_3597_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_msg_3590_, v___y_3592_);
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
lean_inc(v_a_3598_);
lean_dec_ref(v___x_3597_);
v___x_3599_ = l_Lean_Elab_getBetterRef(v_a_3595_, v_macroStack_3596_);
lean_dec(v_a_3595_);
lean_inc(v_macroStack_3596_);
v___x_3600_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11___redArg(v_a_3598_, v_macroStack_3596_, v___y_3592_);
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3603_ = v___x_3600_;
v_isShared_3604_ = v_isSharedCheck_3609_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_a_3601_);
lean_dec(v___x_3600_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3609_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3605_; lean_object* v___x_3607_; 
v___x_3605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3599_);
lean_ctor_set(v___x_3605_, 1, v_a_3601_);
if (v_isShared_3604_ == 0)
{
lean_ctor_set_tag(v___x_3603_, 1);
lean_ctor_set(v___x_3603_, 0, v___x_3605_);
v___x_3607_ = v___x_3603_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v___x_3605_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
return v___x_3607_;
}
}
}
else
{
lean_object* v_a_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3617_; 
lean_dec_ref(v_msg_3590_);
v_a_3610_ = lean_ctor_get(v___x_3594_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3612_ = v___x_3594_;
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_a_3610_);
lean_dec(v___x_3594_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3615_; 
if (v_isShared_3613_ == 0)
{
v___x_3615_ = v___x_3612_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_a_3610_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_msg_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_3618_, v___y_3619_, v___y_3620_);
lean_dec(v___y_3620_);
lean_dec_ref(v___y_3619_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(lean_object* v_ref_3623_, lean_object* v_msg_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_){
_start:
{
lean_object* v___x_3628_; 
v___x_3628_ = l_Lean_Elab_Command_getRef___redArg(v___y_3625_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v_a_3629_; lean_object* v_fileName_3630_; lean_object* v_fileMap_3631_; lean_object* v_currRecDepth_3632_; lean_object* v_cmdPos_3633_; lean_object* v_macroStack_3634_; lean_object* v_quotContext_x3f_3635_; lean_object* v_currMacroScope_3636_; lean_object* v_snap_x3f_3637_; lean_object* v_cancelTk_x3f_3638_; uint8_t v_suppressElabErrors_3639_; lean_object* v_ref_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v_a_3629_ = lean_ctor_get(v___x_3628_, 0);
lean_inc(v_a_3629_);
lean_dec_ref_known(v___x_3628_, 1);
v_fileName_3630_ = lean_ctor_get(v___y_3625_, 0);
v_fileMap_3631_ = lean_ctor_get(v___y_3625_, 1);
v_currRecDepth_3632_ = lean_ctor_get(v___y_3625_, 2);
v_cmdPos_3633_ = lean_ctor_get(v___y_3625_, 3);
v_macroStack_3634_ = lean_ctor_get(v___y_3625_, 4);
v_quotContext_x3f_3635_ = lean_ctor_get(v___y_3625_, 5);
v_currMacroScope_3636_ = lean_ctor_get(v___y_3625_, 6);
v_snap_x3f_3637_ = lean_ctor_get(v___y_3625_, 8);
v_cancelTk_x3f_3638_ = lean_ctor_get(v___y_3625_, 9);
v_suppressElabErrors_3639_ = lean_ctor_get_uint8(v___y_3625_, sizeof(void*)*10);
v_ref_3640_ = l_Lean_replaceRef(v_ref_3623_, v_a_3629_);
lean_dec(v_a_3629_);
lean_inc(v_cancelTk_x3f_3638_);
lean_inc(v_snap_x3f_3637_);
lean_inc(v_currMacroScope_3636_);
lean_inc(v_quotContext_x3f_3635_);
lean_inc(v_macroStack_3634_);
lean_inc(v_cmdPos_3633_);
lean_inc(v_currRecDepth_3632_);
lean_inc_ref(v_fileMap_3631_);
lean_inc_ref(v_fileName_3630_);
v___x_3641_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_3641_, 0, v_fileName_3630_);
lean_ctor_set(v___x_3641_, 1, v_fileMap_3631_);
lean_ctor_set(v___x_3641_, 2, v_currRecDepth_3632_);
lean_ctor_set(v___x_3641_, 3, v_cmdPos_3633_);
lean_ctor_set(v___x_3641_, 4, v_macroStack_3634_);
lean_ctor_set(v___x_3641_, 5, v_quotContext_x3f_3635_);
lean_ctor_set(v___x_3641_, 6, v_currMacroScope_3636_);
lean_ctor_set(v___x_3641_, 7, v_ref_3640_);
lean_ctor_set(v___x_3641_, 8, v_snap_x3f_3637_);
lean_ctor_set(v___x_3641_, 9, v_cancelTk_x3f_3638_);
lean_ctor_set_uint8(v___x_3641_, sizeof(void*)*10, v_suppressElabErrors_3639_);
v___x_3642_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_3624_, v___x_3641_, v___y_3626_);
lean_dec_ref_known(v___x_3641_, 10);
return v___x_3642_;
}
else
{
lean_object* v_a_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3650_; 
lean_dec_ref(v_msg_3624_);
v_a_3643_ = lean_ctor_get(v___x_3628_, 0);
v_isSharedCheck_3650_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3645_ = v___x_3628_;
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_a_3643_);
lean_dec(v___x_3628_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3648_; 
if (v_isShared_3646_ == 0)
{
v___x_3648_ = v___x_3645_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v_a_3643_);
v___x_3648_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
return v___x_3648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_ref_3651_, lean_object* v_msg_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_){
_start:
{
lean_object* v_res_3656_; 
v_res_3656_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v_ref_3651_, v_msg_3652_, v___y_3653_, v___y_3654_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v_ref_3651_);
return v_res_3656_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3658_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__0));
v___x_3659_ = l_Lean_stringToMessageData(v___x_3658_);
return v___x_3659_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; 
v___x_3661_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__2));
v___x_3662_ = l_Lean_stringToMessageData(v___x_3661_);
return v___x_3662_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3664_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__4));
v___x_3665_ = l_Lean_stringToMessageData(v___x_3664_);
return v___x_3665_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3667_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__6));
v___x_3668_ = l_Lean_stringToMessageData(v___x_3667_);
return v___x_3668_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3670_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__8));
v___x_3671_ = l_Lean_stringToMessageData(v___x_3670_);
return v___x_3671_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__11(void){
_start:
{
lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3673_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__10));
v___x_3674_ = l_Lean_stringToMessageData(v___x_3673_);
return v___x_3674_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__13(void){
_start:
{
lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3676_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__12));
v___x_3677_ = l_Lean_stringToMessageData(v___x_3676_);
return v___x_3677_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_msg_3678_, lean_object* v_declHint_3679_, lean_object* v___y_3680_){
_start:
{
lean_object* v___x_3682_; lean_object* v_env_3683_; uint8_t v___x_3684_; 
v___x_3682_ = lean_st_ref_get(v___y_3680_);
v_env_3683_ = lean_ctor_get(v___x_3682_, 0);
lean_inc_ref(v_env_3683_);
lean_dec(v___x_3682_);
v___x_3684_ = l_Lean_Name_isAnonymous(v_declHint_3679_);
if (v___x_3684_ == 0)
{
uint8_t v_isExporting_3685_; 
v_isExporting_3685_ = lean_ctor_get_uint8(v_env_3683_, sizeof(void*)*8);
if (v_isExporting_3685_ == 0)
{
lean_object* v___x_3686_; 
lean_dec_ref(v_env_3683_);
lean_dec(v_declHint_3679_);
v___x_3686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3686_, 0, v_msg_3678_);
return v___x_3686_;
}
else
{
lean_object* v___x_3687_; uint8_t v___x_3688_; 
lean_inc_ref(v_env_3683_);
v___x_3687_ = l_Lean_Environment_setExporting(v_env_3683_, v___x_3684_);
lean_inc(v_declHint_3679_);
lean_inc_ref(v___x_3687_);
v___x_3688_ = l_Lean_Environment_contains(v___x_3687_, v_declHint_3679_, v_isExporting_3685_);
if (v___x_3688_ == 0)
{
lean_object* v___x_3689_; 
lean_dec_ref(v___x_3687_);
lean_dec_ref(v_env_3683_);
lean_dec(v_declHint_3679_);
v___x_3689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3689_, 0, v_msg_3678_);
return v___x_3689_;
}
else
{
lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v_c_3695_; lean_object* v___x_3696_; 
v___x_3690_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2);
v___x_3691_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5);
v___x_3692_ = l_Lean_Options_empty;
v___x_3693_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3687_);
lean_ctor_set(v___x_3693_, 1, v___x_3690_);
lean_ctor_set(v___x_3693_, 2, v___x_3691_);
lean_ctor_set(v___x_3693_, 3, v___x_3692_);
lean_inc(v_declHint_3679_);
v___x_3694_ = l_Lean_MessageData_ofConstName(v_declHint_3679_, v___x_3684_);
v_c_3695_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3695_, 0, v___x_3693_);
lean_ctor_set(v_c_3695_, 1, v___x_3694_);
v___x_3696_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3683_, v_declHint_3679_);
if (lean_obj_tag(v___x_3696_) == 0)
{
lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; 
lean_dec_ref(v_env_3683_);
lean_dec(v_declHint_3679_);
v___x_3697_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_3698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3698_, 0, v___x_3697_);
lean_ctor_set(v___x_3698_, 1, v_c_3695_);
v___x_3699_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_3700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3700_, 0, v___x_3698_);
lean_ctor_set(v___x_3700_, 1, v___x_3699_);
v___x_3701_ = l_Lean_MessageData_note(v___x_3700_);
v___x_3702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3702_, 0, v_msg_3678_);
lean_ctor_set(v___x_3702_, 1, v___x_3701_);
v___x_3703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3702_);
return v___x_3703_;
}
else
{
lean_object* v_val_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3739_; 
v_val_3704_ = lean_ctor_get(v___x_3696_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3706_ = v___x_3696_;
v_isShared_3707_ = v_isSharedCheck_3739_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_val_3704_);
lean_dec(v___x_3696_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3739_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v_mod_3711_; uint8_t v___x_3712_; 
v___x_3708_ = lean_box(0);
v___x_3709_ = l_Lean_Environment_header(v_env_3683_);
lean_dec_ref(v_env_3683_);
v___x_3710_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3709_);
v_mod_3711_ = lean_array_get(v___x_3708_, v___x_3710_, v_val_3704_);
lean_dec(v_val_3704_);
lean_dec_ref(v___x_3710_);
v___x_3712_ = l_Lean_isPrivateName(v_declHint_3679_);
lean_dec(v_declHint_3679_);
if (v___x_3712_ == 0)
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3724_; 
v___x_3713_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__5);
v___x_3714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3713_);
lean_ctor_set(v___x_3714_, 1, v_c_3695_);
v___x_3715_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_3716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3714_);
lean_ctor_set(v___x_3716_, 1, v___x_3715_);
v___x_3717_ = l_Lean_MessageData_ofName(v_mod_3711_);
v___x_3718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3716_);
lean_ctor_set(v___x_3718_, 1, v___x_3717_);
v___x_3719_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__9);
v___x_3720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3718_);
lean_ctor_set(v___x_3720_, 1, v___x_3719_);
v___x_3721_ = l_Lean_MessageData_note(v___x_3720_);
v___x_3722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3722_, 0, v_msg_3678_);
lean_ctor_set(v___x_3722_, 1, v___x_3721_);
if (v_isShared_3707_ == 0)
{
lean_ctor_set_tag(v___x_3706_, 0);
lean_ctor_set(v___x_3706_, 0, v___x_3722_);
v___x_3724_ = v___x_3706_;
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
else
{
lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3737_; 
v___x_3726_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_3727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3726_);
lean_ctor_set(v___x_3727_, 1, v_c_3695_);
v___x_3728_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__11);
v___x_3729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3727_);
lean_ctor_set(v___x_3729_, 1, v___x_3728_);
v___x_3730_ = l_Lean_MessageData_ofName(v_mod_3711_);
v___x_3731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3729_);
lean_ctor_set(v___x_3731_, 1, v___x_3730_);
v___x_3732_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__13);
v___x_3733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3731_);
lean_ctor_set(v___x_3733_, 1, v___x_3732_);
v___x_3734_ = l_Lean_MessageData_note(v___x_3733_);
v___x_3735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3735_, 0, v_msg_3678_);
lean_ctor_set(v___x_3735_, 1, v___x_3734_);
if (v_isShared_3707_ == 0)
{
lean_ctor_set_tag(v___x_3706_, 0);
lean_ctor_set(v___x_3706_, 0, v___x_3735_);
v___x_3737_ = v___x_3706_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v___x_3735_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3740_; 
lean_dec_ref(v_env_3683_);
lean_dec(v_declHint_3679_);
v___x_3740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3740_, 0, v_msg_3678_);
return v___x_3740_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_msg_3741_, lean_object* v_declHint_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_){
_start:
{
lean_object* v_res_3745_; 
v_res_3745_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_3741_, v_declHint_3742_, v___y_3743_);
lean_dec(v___y_3743_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6(lean_object* v_msg_3746_, lean_object* v_declHint_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_){
_start:
{
lean_object* v___x_3751_; lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3761_; 
v___x_3751_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_3746_, v_declHint_3747_, v___y_3749_);
v_a_3752_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3754_ = v___x_3751_;
v_isShared_3755_ = v_isSharedCheck_3761_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3751_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3761_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3759_; 
v___x_3756_ = l_Lean_unknownIdentifierMessageTag;
v___x_3757_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3756_);
lean_ctor_set(v___x_3757_, 1, v_a_3752_);
if (v_isShared_3755_ == 0)
{
lean_ctor_set(v___x_3754_, 0, v___x_3757_);
v___x_3759_ = v___x_3754_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v___x_3757_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___boxed(lean_object* v_msg_3762_, lean_object* v_declHint_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_){
_start:
{
lean_object* v_res_3767_; 
v_res_3767_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_3762_, v_declHint_3763_, v___y_3764_, v___y_3765_);
lean_dec(v___y_3765_);
lean_dec_ref(v___y_3764_);
return v_res_3767_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_3768_, lean_object* v_msg_3769_, lean_object* v_declHint_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_){
_start:
{
lean_object* v___x_3774_; lean_object* v_a_3775_; lean_object* v___x_3776_; 
v___x_3774_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_3769_, v_declHint_3770_, v___y_3771_, v___y_3772_);
v_a_3775_ = lean_ctor_get(v___x_3774_, 0);
lean_inc(v_a_3775_);
lean_dec_ref(v___x_3774_);
v___x_3776_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v_ref_3768_, v_a_3775_, v___y_3771_, v___y_3772_);
return v___x_3776_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_3777_, lean_object* v_msg_3778_, lean_object* v_declHint_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3777_, v_msg_3778_, v_declHint_3779_, v___y_3780_, v___y_3781_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
lean_dec(v_ref_3777_);
return v_res_3783_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3785_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___closed__0));
v___x_3786_ = l_Lean_stringToMessageData(v___x_3785_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_3787_, lean_object* v_constName_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_){
_start:
{
lean_object* v___x_3792_; uint8_t v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3792_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_3793_ = 0;
lean_inc(v_constName_3788_);
v___x_3794_ = l_Lean_MessageData_ofConstName(v_constName_3788_, v___x_3793_);
v___x_3795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3795_, 0, v___x_3792_);
lean_ctor_set(v___x_3795_, 1, v___x_3794_);
v___x_3796_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1);
v___x_3797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3797_, 0, v___x_3795_);
lean_ctor_set(v___x_3797_, 1, v___x_3796_);
v___x_3798_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3787_, v___x_3797_, v_constName_3788_, v___y_3789_, v___y_3790_);
return v___x_3798_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_3799_, lean_object* v_constName_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_){
_start:
{
lean_object* v_res_3804_; 
v_res_3804_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3799_, v_constName_3800_, v___y_3801_, v___y_3802_);
lean_dec(v___y_3802_);
lean_dec_ref(v___y_3801_);
lean_dec(v_ref_3799_);
return v_res_3804_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_){
_start:
{
lean_object* v___x_3809_; 
v___x_3809_ = l_Lean_Elab_Command_getRef___redArg(v___y_3806_);
if (lean_obj_tag(v___x_3809_) == 0)
{
lean_object* v_a_3810_; lean_object* v___x_3811_; 
v_a_3810_ = lean_ctor_get(v___x_3809_, 0);
lean_inc(v_a_3810_);
lean_dec_ref_known(v___x_3809_, 1);
v___x_3811_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_a_3810_, v_constName_3805_, v___y_3806_, v___y_3807_);
lean_dec(v_a_3810_);
return v___x_3811_;
}
else
{
lean_object* v_a_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3819_; 
lean_dec(v_constName_3805_);
v_a_3812_ = lean_ctor_get(v___x_3809_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3809_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3814_ = v___x_3809_;
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_a_3812_);
lean_dec(v___x_3809_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3817_; 
if (v_isShared_3815_ == 0)
{
v___x_3817_ = v___x_3814_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_a_3812_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
return v___x_3817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_){
_start:
{
lean_object* v_res_3824_; 
v_res_3824_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1___redArg(v_constName_3820_, v___y_3821_, v___y_3822_);
lean_dec(v___y_3822_);
lean_dec_ref(v___y_3821_);
return v_res_3824_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0(lean_object* v_constName_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
lean_object* v___x_3829_; lean_object* v_env_3830_; uint8_t v___x_3831_; lean_object* v___x_3832_; 
v___x_3829_ = lean_st_ref_get(v___y_3827_);
v_env_3830_ = lean_ctor_get(v___x_3829_, 0);
lean_inc_ref(v_env_3830_);
lean_dec(v___x_3829_);
v___x_3831_ = 0;
lean_inc(v_constName_3825_);
v___x_3832_ = l_Lean_Environment_find_x3f(v_env_3830_, v_constName_3825_, v___x_3831_);
if (lean_obj_tag(v___x_3832_) == 0)
{
lean_object* v___x_3833_; 
v___x_3833_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1___redArg(v_constName_3825_, v___y_3826_, v___y_3827_);
return v___x_3833_;
}
else
{
lean_object* v_val_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3841_; 
lean_dec(v_constName_3825_);
v_val_3834_ = lean_ctor_get(v___x_3832_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3836_ = v___x_3832_;
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_val_3834_);
lean_dec(v___x_3832_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3839_; 
if (v_isShared_3837_ == 0)
{
lean_ctor_set_tag(v___x_3836_, 0);
v___x_3839_ = v___x_3836_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_val_3834_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0___boxed(lean_object* v_constName_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_){
_start:
{
lean_object* v_res_3846_; 
v_res_3846_ = l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0(v_constName_3842_, v___y_3843_, v___y_3844_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
return v_res_3846_;
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__1(uint8_t v___x_3847_, lean_object* v_x_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_){
_start:
{
if (lean_obj_tag(v_x_3848_) == 0)
{
uint8_t v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; 
v___x_3852_ = 1;
v___x_3853_ = lean_box(v___x_3852_);
v___x_3854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3854_, 0, v___x_3853_);
return v___x_3854_;
}
else
{
lean_object* v_head_3855_; lean_object* v_tail_3856_; lean_object* v___x_3857_; 
v_head_3855_ = lean_ctor_get(v_x_3848_, 0);
lean_inc(v_head_3855_);
v_tail_3856_ = lean_ctor_get(v_x_3848_, 1);
lean_inc(v_tail_3856_);
lean_dec_ref_known(v_x_3848_, 2);
v___x_3857_ = l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0(v_head_3855_, v___y_3849_, v___y_3850_);
if (lean_obj_tag(v___x_3857_) == 0)
{
lean_object* v_a_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3878_; 
v_a_3858_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_3878_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3878_ == 0)
{
v___x_3860_ = v___x_3857_;
v_isShared_3861_ = v_isSharedCheck_3878_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_a_3858_);
lean_dec(v___x_3857_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3878_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
lean_object* v___y_3863_; uint8_t v_a_3864_; 
if (lean_obj_tag(v_a_3858_) == 6)
{
lean_object* v_val_3866_; lean_object* v_numFields_3867_; lean_object* v___x_3868_; uint8_t v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3872_; 
v_val_3866_ = lean_ctor_get(v_a_3858_, 0);
lean_inc_ref(v_val_3866_);
lean_dec_ref_known(v_a_3858_, 1);
v_numFields_3867_ = lean_ctor_get(v_val_3866_, 4);
lean_inc(v_numFields_3867_);
lean_dec_ref(v_val_3866_);
v___x_3868_ = lean_unsigned_to_nat(0u);
v___x_3869_ = lean_nat_dec_eq(v_numFields_3867_, v___x_3868_);
lean_dec(v_numFields_3867_);
v___x_3870_ = lean_box(v___x_3869_);
if (v_isShared_3861_ == 0)
{
lean_ctor_set(v___x_3860_, 0, v___x_3870_);
v___x_3872_ = v___x_3860_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v___x_3870_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
v___y_3863_ = v___x_3872_;
v_a_3864_ = v___x_3869_;
goto v___jp_3862_;
}
}
else
{
lean_object* v___x_3874_; lean_object* v___x_3876_; 
lean_dec(v_a_3858_);
v___x_3874_ = lean_box(v___x_3847_);
if (v_isShared_3861_ == 0)
{
lean_ctor_set(v___x_3860_, 0, v___x_3874_);
v___x_3876_ = v___x_3860_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v___x_3874_);
v___x_3876_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
v___y_3863_ = v___x_3876_;
v_a_3864_ = v___x_3847_;
goto v___jp_3862_;
}
}
v___jp_3862_:
{
if (v_a_3864_ == 0)
{
lean_dec(v_tail_3856_);
return v___y_3863_;
}
else
{
lean_dec_ref(v___y_3863_);
v_x_3848_ = v_tail_3856_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3886_; 
lean_dec(v_tail_3856_);
v_a_3879_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_3886_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3881_ = v___x_3857_;
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_a_3879_);
lean_dec(v___x_3857_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3884_; 
if (v_isShared_3882_ == 0)
{
v___x_3884_ = v___x_3881_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_a_3879_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__1___boxed(lean_object* v___x_3887_, lean_object* v_x_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_){
_start:
{
uint8_t v___x_4422__boxed_3892_; lean_object* v_res_3893_; 
v___x_4422__boxed_3892_ = lean_unbox(v___x_3887_);
v_res_3893_ = l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__1(v___x_4422__boxed_3892_, v_x_3888_, v___y_3889_, v___y_3890_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
return v_res_3893_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0(lean_object* v_declName_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_){
_start:
{
lean_object* v___x_3898_; 
v___x_3898_ = l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0(v_declName_3894_, v___y_3895_, v___y_3896_);
if (lean_obj_tag(v___x_3898_) == 0)
{
lean_object* v_a_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3954_; 
v_a_3899_ = lean_ctor_get(v___x_3898_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v___x_3898_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3901_ = v___x_3898_;
v_isShared_3902_ = v_isSharedCheck_3954_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_a_3899_);
lean_dec(v___x_3898_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3954_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
if (lean_obj_tag(v_a_3899_) == 5)
{
lean_object* v_val_3903_; lean_object* v_toConstantVal_3904_; lean_object* v_numParams_3905_; lean_object* v_numIndices_3906_; lean_object* v_ctors_3907_; uint8_t v_isRec_3908_; uint8_t v_isUnsafe_3909_; lean_object* v_type_3910_; uint8_t v___x_3911_; 
v_val_3903_ = lean_ctor_get(v_a_3899_, 0);
lean_inc_ref(v_val_3903_);
lean_dec_ref_known(v_a_3899_, 1);
v_toConstantVal_3904_ = lean_ctor_get(v_val_3903_, 0);
v_numParams_3905_ = lean_ctor_get(v_val_3903_, 1);
lean_inc(v_numParams_3905_);
v_numIndices_3906_ = lean_ctor_get(v_val_3903_, 2);
lean_inc(v_numIndices_3906_);
v_ctors_3907_ = lean_ctor_get(v_val_3903_, 4);
lean_inc(v_ctors_3907_);
v_isRec_3908_ = lean_ctor_get_uint8(v_val_3903_, sizeof(void*)*6);
v_isUnsafe_3909_ = lean_ctor_get_uint8(v_val_3903_, sizeof(void*)*6 + 1);
v_type_3910_ = lean_ctor_get(v_toConstantVal_3904_, 2);
v___x_3911_ = l_Lean_Expr_isProp(v_type_3910_);
if (v___x_3911_ == 0)
{
lean_object* v___x_3912_; lean_object* v___x_3913_; uint8_t v___x_3914_; 
v___x_3912_ = l_Lean_InductiveVal_numTypeFormers(v_val_3903_);
lean_dec_ref(v_val_3903_);
v___x_3913_ = lean_unsigned_to_nat(1u);
v___x_3914_ = lean_nat_dec_eq(v___x_3912_, v___x_3913_);
lean_dec(v___x_3912_);
if (v___x_3914_ == 0)
{
lean_object* v___x_3915_; lean_object* v___x_3917_; 
lean_dec(v_ctors_3907_);
lean_dec(v_numIndices_3906_);
lean_dec(v_numParams_3905_);
v___x_3915_ = lean_box(v___x_3914_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 0, v___x_3915_);
v___x_3917_ = v___x_3901_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v___x_3915_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
return v___x_3917_;
}
}
else
{
lean_object* v___x_3919_; uint8_t v___x_3920_; 
v___x_3919_ = lean_unsigned_to_nat(0u);
v___x_3920_ = lean_nat_dec_eq(v_numIndices_3906_, v___x_3919_);
lean_dec(v_numIndices_3906_);
if (v___x_3920_ == 0)
{
lean_object* v___x_3921_; lean_object* v___x_3923_; 
lean_dec(v_ctors_3907_);
lean_dec(v_numParams_3905_);
v___x_3921_ = lean_box(v___x_3920_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 0, v___x_3921_);
v___x_3923_ = v___x_3901_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v___x_3921_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
return v___x_3923_;
}
}
else
{
uint8_t v___x_3925_; 
v___x_3925_ = lean_nat_dec_eq(v_numParams_3905_, v___x_3919_);
lean_dec(v_numParams_3905_);
if (v___x_3925_ == 0)
{
lean_object* v___x_3926_; lean_object* v___x_3928_; 
lean_dec(v_ctors_3907_);
v___x_3926_ = lean_box(v___x_3925_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 0, v___x_3926_);
v___x_3928_ = v___x_3901_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v___x_3926_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
else
{
uint8_t v___x_3930_; 
v___x_3930_ = l_List_isEmpty___redArg(v_ctors_3907_);
if (v___x_3930_ == 0)
{
if (v_isRec_3908_ == 0)
{
if (v_isUnsafe_3909_ == 0)
{
lean_object* v___x_3931_; 
lean_del_object(v___x_3901_);
v___x_3931_ = l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__1(v_isUnsafe_3909_, v_ctors_3907_, v___y_3895_, v___y_3896_);
return v___x_3931_;
}
else
{
lean_object* v___x_3932_; lean_object* v___x_3934_; 
lean_dec(v_ctors_3907_);
v___x_3932_ = lean_box(v_isRec_3908_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 0, v___x_3932_);
v___x_3934_ = v___x_3901_;
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
lean_object* v___x_3936_; lean_object* v___x_3938_; 
lean_dec(v_ctors_3907_);
v___x_3936_ = lean_box(v___x_3930_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 0, v___x_3936_);
v___x_3938_ = v___x_3901_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v___x_3936_);
v___x_3938_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
return v___x_3938_;
}
}
}
else
{
lean_object* v___x_3940_; lean_object* v___x_3942_; 
lean_dec(v_ctors_3907_);
v___x_3940_ = lean_box(v___x_3911_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 0, v___x_3940_);
v___x_3942_ = v___x_3901_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v___x_3940_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
}
}
}
}
else
{
uint8_t v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3947_; 
lean_dec(v_ctors_3907_);
lean_dec(v_numIndices_3906_);
lean_dec(v_numParams_3905_);
lean_dec_ref(v_val_3903_);
v___x_3944_ = 0;
v___x_3945_ = lean_box(v___x_3944_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 0, v___x_3945_);
v___x_3947_ = v___x_3901_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v___x_3945_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
}
}
}
else
{
uint8_t v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3952_; 
lean_dec(v_a_3899_);
v___x_3949_ = 0;
v___x_3950_ = lean_box(v___x_3949_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 0, v___x_3950_);
v___x_3952_ = v___x_3901_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v___x_3950_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
}
}
else
{
lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3962_; 
v_a_3955_ = lean_ctor_get(v___x_3898_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3898_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3957_ = v___x_3898_;
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v___x_3898_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3960_; 
if (v_isShared_3958_ == 0)
{
v___x_3960_ = v___x_3957_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_a_3955_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0___boxed(lean_object* v_declName_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_){
_start:
{
lean_object* v_res_3967_; 
v_res_3967_ = l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0(v_declName_3963_, v___y_3964_, v___y_3965_);
lean_dec(v___y_3965_);
lean_dec_ref(v___y_3964_);
return v_res_3967_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__1(lean_object* v_as_3968_, size_t v_i_3969_, size_t v_stop_3970_, lean_object* v_b_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_){
_start:
{
uint8_t v___x_3975_; 
v___x_3975_ = lean_usize_dec_eq(v_i_3969_, v_stop_3970_);
if (v___x_3975_ == 0)
{
lean_object* v___x_3976_; lean_object* v___x_3977_; 
v___x_3976_ = lean_array_uget_borrowed(v_as_3968_, v_i_3969_);
lean_inc(v___x_3976_);
v___x_3977_ = l_Lean_Elab_Command_elabCommand(v___x_3976_, v___y_3972_, v___y_3973_);
if (lean_obj_tag(v___x_3977_) == 0)
{
lean_object* v_a_3978_; size_t v___x_3979_; size_t v___x_3980_; 
v_a_3978_ = lean_ctor_get(v___x_3977_, 0);
lean_inc(v_a_3978_);
lean_dec_ref_known(v___x_3977_, 1);
v___x_3979_ = ((size_t)1ULL);
v___x_3980_ = lean_usize_add(v_i_3969_, v___x_3979_);
v_i_3969_ = v___x_3980_;
v_b_3971_ = v_a_3978_;
goto _start;
}
else
{
return v___x_3977_;
}
}
else
{
lean_object* v___x_3982_; 
v___x_3982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3982_, 0, v_b_3971_);
return v___x_3982_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__1___boxed(lean_object* v_as_3983_, lean_object* v_i_3984_, lean_object* v_stop_3985_, lean_object* v_b_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_){
_start:
{
size_t v_i_boxed_3990_; size_t v_stop_boxed_3991_; lean_object* v_res_3992_; 
v_i_boxed_3990_ = lean_unbox_usize(v_i_3984_);
lean_dec(v_i_3984_);
v_stop_boxed_3991_ = lean_unbox_usize(v_stop_3985_);
lean_dec(v_stop_3985_);
v_res_3992_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__1(v_as_3983_, v_i_boxed_3990_, v_stop_boxed_3991_, v_b_3986_, v___y_3987_, v___y_3988_);
lean_dec(v___y_3988_);
lean_dec_ref(v___y_3987_);
lean_dec_ref(v_as_3983_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__1(lean_object* v_declName_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_){
_start:
{
lean_object* v___x_3997_; 
lean_inc(v_declName_3993_);
v___x_3997_ = l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0(v_declName_3993_, v___y_3994_, v___y_3995_);
if (lean_obj_tag(v___x_3997_) == 0)
{
lean_object* v_a_3998_; lean_object* v___y_3999_; lean_object* v___x_4000_; 
v_a_3998_ = lean_ctor_get(v___x_3997_, 0);
lean_inc(v_a_3998_);
lean_dec_ref_known(v___x_3997_, 1);
v___y_3999_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__0___boxed), 9, 2);
lean_closure_set(v___y_3999_, 0, v_a_3998_);
lean_closure_set(v___y_3999_, 1, v_declName_3993_);
v___x_4000_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___y_3999_, v___y_3994_, v___y_3995_);
if (lean_obj_tag(v___x_4000_) == 0)
{
lean_object* v_a_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4022_; 
v_a_4001_ = lean_ctor_get(v___x_4000_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_4000_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4003_ = v___x_4000_;
v_isShared_4004_ = v_isSharedCheck_4022_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_a_4001_);
lean_dec(v___x_4000_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4022_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; uint8_t v___x_4008_; 
v___x_4005_ = lean_unsigned_to_nat(0u);
v___x_4006_ = lean_array_get_size(v_a_4001_);
v___x_4007_ = lean_box(0);
v___x_4008_ = lean_nat_dec_lt(v___x_4005_, v___x_4006_);
if (v___x_4008_ == 0)
{
lean_object* v___x_4010_; 
lean_dec(v_a_4001_);
if (v_isShared_4004_ == 0)
{
lean_ctor_set(v___x_4003_, 0, v___x_4007_);
v___x_4010_ = v___x_4003_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v___x_4007_);
v___x_4010_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
return v___x_4010_;
}
}
else
{
uint8_t v___x_4012_; 
v___x_4012_ = lean_nat_dec_le(v___x_4006_, v___x_4006_);
if (v___x_4012_ == 0)
{
if (v___x_4008_ == 0)
{
lean_object* v___x_4014_; 
lean_dec(v_a_4001_);
if (v_isShared_4004_ == 0)
{
lean_ctor_set(v___x_4003_, 0, v___x_4007_);
v___x_4014_ = v___x_4003_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v___x_4007_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
return v___x_4014_;
}
}
else
{
size_t v___x_4016_; size_t v___x_4017_; lean_object* v___x_4018_; 
lean_del_object(v___x_4003_);
v___x_4016_ = ((size_t)0ULL);
v___x_4017_ = lean_usize_of_nat(v___x_4006_);
v___x_4018_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__1(v_a_4001_, v___x_4016_, v___x_4017_, v___x_4007_, v___y_3994_, v___y_3995_);
lean_dec(v_a_4001_);
return v___x_4018_;
}
}
else
{
size_t v___x_4019_; size_t v___x_4020_; lean_object* v___x_4021_; 
lean_del_object(v___x_4003_);
v___x_4019_ = ((size_t)0ULL);
v___x_4020_ = lean_usize_of_nat(v___x_4006_);
v___x_4021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__1(v_a_4001_, v___x_4019_, v___x_4020_, v___x_4007_, v___y_3994_, v___y_3995_);
lean_dec(v_a_4001_);
return v___x_4021_;
}
}
}
}
else
{
lean_object* v_a_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4030_; 
v_a_4023_ = lean_ctor_get(v___x_4000_, 0);
v_isSharedCheck_4030_ = !lean_is_exclusive(v___x_4000_);
if (v_isSharedCheck_4030_ == 0)
{
v___x_4025_ = v___x_4000_;
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_a_4023_);
lean_dec(v___x_4000_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v___x_4028_; 
if (v_isShared_4026_ == 0)
{
v___x_4028_ = v___x_4025_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v_a_4023_);
v___x_4028_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
return v___x_4028_;
}
}
}
}
else
{
lean_object* v_a_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4038_; 
lean_dec(v_declName_3993_);
v_a_4031_ = lean_ctor_get(v___x_3997_, 0);
v_isSharedCheck_4038_ = !lean_is_exclusive(v___x_3997_);
if (v_isSharedCheck_4038_ == 0)
{
v___x_4033_ = v___x_3997_;
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_a_4031_);
lean_dec(v___x_3997_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
lean_object* v___x_4036_; 
if (v_isShared_4034_ == 0)
{
v___x_4036_ = v___x_4033_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_a_4031_);
v___x_4036_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
return v___x_4036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__1___boxed(lean_object* v_declName_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_){
_start:
{
lean_object* v_res_4043_; 
v_res_4043_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__1(v_declName_4039_, v___y_4040_, v___y_4041_);
lean_dec(v___y_4041_);
lean_dec_ref(v___y_4040_);
return v_res_4043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance(lean_object* v_declName_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_){
_start:
{
lean_object* v___f_4048_; lean_object* v___x_4049_; 
lean_inc(v_declName_4044_);
v___f_4048_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__1___boxed), 4, 1);
lean_closure_set(v___f_4048_, 0, v_declName_4044_);
v___x_4049_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_declName_4044_, v___f_4048_, v_a_4045_, v_a_4046_);
return v___x_4049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___boxed(lean_object* v_declName_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_){
_start:
{
lean_object* v_res_4054_; 
v_res_4054_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance(v_declName_4050_, v_a_4051_, v_a_4052_);
lean_dec(v_a_4052_);
lean_dec_ref(v_a_4051_);
return v_res_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4055_, lean_object* v_constName_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_){
_start:
{
lean_object* v___x_4060_; 
v___x_4060_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1___redArg(v_constName_4056_, v___y_4057_, v___y_4058_);
return v___x_4060_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_4061_, lean_object* v_constName_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_){
_start:
{
lean_object* v_res_4066_; 
v_res_4066_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1(v_00_u03b1_4061_, v_constName_4062_, v___y_4063_, v___y_4064_);
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4063_);
return v_res_4066_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_4067_, lean_object* v_ref_4068_, lean_object* v_constName_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_){
_start:
{
lean_object* v___x_4073_; 
v___x_4073_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_4068_, v_constName_4069_, v___y_4070_, v___y_4071_);
return v___x_4073_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4074_, lean_object* v_ref_4075_, lean_object* v_constName_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_){
_start:
{
lean_object* v_res_4080_; 
v_res_4080_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_4074_, v_ref_4075_, v_constName_4076_, v___y_4077_, v___y_4078_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec(v_ref_4075_);
return v_res_4080_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_4081_, lean_object* v_ref_4082_, lean_object* v_msg_4083_, lean_object* v_declHint_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_){
_start:
{
lean_object* v___x_4088_; 
v___x_4088_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_4082_, v_msg_4083_, v_declHint_4084_, v___y_4085_, v___y_4086_);
return v___x_4088_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_4089_, lean_object* v_ref_4090_, lean_object* v_msg_4091_, lean_object* v_declHint_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_){
_start:
{
lean_object* v_res_4096_; 
v_res_4096_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_4089_, v_ref_4090_, v_msg_4091_, v_declHint_4092_, v___y_4093_, v___y_4094_);
lean_dec(v___y_4094_);
lean_dec_ref(v___y_4093_);
lean_dec(v_ref_4090_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7(lean_object* v_msg_4097_, lean_object* v_declHint_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
lean_object* v___x_4102_; 
v___x_4102_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_4097_, v_declHint_4098_, v___y_4100_);
return v___x_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___boxed(lean_object* v_msg_4103_, lean_object* v_declHint_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_){
_start:
{
lean_object* v_res_4108_; 
v_res_4108_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7(v_msg_4103_, v_declHint_4104_, v___y_4105_, v___y_4106_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
return v_res_4108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_4109_, lean_object* v_ref_4110_, lean_object* v_msg_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_){
_start:
{
lean_object* v___x_4115_; 
v___x_4115_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v_ref_4110_, v_msg_4111_, v___y_4112_, v___y_4113_);
return v___x_4115_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_4116_, lean_object* v_ref_4117_, lean_object* v_msg_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_){
_start:
{
lean_object* v_res_4122_; 
v_res_4122_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7(v_00_u03b1_4116_, v_ref_4117_, v_msg_4118_, v___y_4119_, v___y_4120_);
lean_dec(v___y_4120_);
lean_dec_ref(v___y_4119_);
lean_dec(v_ref_4117_);
return v_res_4122_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10(lean_object* v_msgData_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_){
_start:
{
lean_object* v___x_4127_; 
v___x_4127_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_msgData_4123_, v___y_4125_);
return v___x_4127_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___boxed(lean_object* v_msgData_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_){
_start:
{
lean_object* v_res_4132_; 
v_res_4132_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10(v_msgData_4128_, v___y_4129_, v___y_4130_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
return v_res_4132_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_4133_, lean_object* v_msg_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_){
_start:
{
lean_object* v___x_4138_; 
v___x_4138_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_4134_, v___y_4135_, v___y_4136_);
return v___x_4138_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4139_, lean_object* v_msg_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_){
_start:
{
lean_object* v_res_4144_; 
v_res_4144_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9(v_00_u03b1_4139_, v_msg_4140_, v___y_4141_, v___y_4142_);
lean_dec(v___y_4142_);
lean_dec_ref(v___y_4141_);
return v_res_4144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11(lean_object* v_msgData_4145_, lean_object* v_macroStack_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_){
_start:
{
lean_object* v___x_4150_; 
v___x_4150_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11___redArg(v_msgData_4145_, v_macroStack_4146_, v___y_4148_);
return v___x_4150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11___boxed(lean_object* v_msgData_4151_, lean_object* v_macroStack_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_){
_start:
{
lean_object* v_res_4156_; 
v_res_4156_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11(v_msgData_4151_, v_macroStack_4152_, v___y_4153_, v___y_4154_);
lean_dec(v___y_4154_);
lean_dec_ref(v___y_4153_);
return v_res_4156_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1___redArg(lean_object* v_declName_4157_, lean_object* v___y_4158_){
_start:
{
lean_object* v___x_4160_; lean_object* v_env_4161_; uint8_t v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; 
v___x_4160_ = lean_st_ref_get(v___y_4158_);
v_env_4161_ = lean_ctor_get(v___x_4160_, 0);
lean_inc_ref(v_env_4161_);
lean_dec(v___x_4160_);
v___x_4162_ = l_Lean_isInductiveCore(v_env_4161_, v_declName_4157_);
v___x_4163_ = lean_box(v___x_4162_);
v___x_4164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4163_);
return v___x_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1___redArg___boxed(lean_object* v_declName_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_){
_start:
{
lean_object* v_res_4168_; 
v_res_4168_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1___redArg(v_declName_4165_, v___y_4166_);
lean_dec(v___y_4166_);
return v_res_4168_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1(lean_object* v_declName_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v___x_4173_; 
v___x_4173_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1___redArg(v_declName_4169_, v___y_4171_);
return v___x_4173_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1___boxed(lean_object* v_declName_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_){
_start:
{
lean_object* v_res_4178_; 
v_res_4178_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1(v_declName_4174_, v___y_4175_, v___y_4176_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___lam__0(uint8_t v_____do__lift_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_){
_start:
{
if (v_____do__lift_4179_ == 0)
{
uint8_t v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; 
v___x_4183_ = 1;
v___x_4184_ = lean_box(v___x_4183_);
v___x_4185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4185_, 0, v___x_4184_);
return v___x_4185_;
}
else
{
uint8_t v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4186_ = 0;
v___x_4187_ = lean_box(v___x_4186_);
v___x_4188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4188_, 0, v___x_4187_);
return v___x_4188_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_){
_start:
{
uint8_t v_____do__lift_1654__boxed_4193_; lean_object* v_res_4194_; 
v_____do__lift_1654__boxed_4193_ = lean_unbox(v_____do__lift_4189_);
v_res_4194_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___lam__0(v_____do__lift_1654__boxed_4193_, v___y_4190_, v___y_4191_);
lean_dec(v___y_4191_);
lean_dec_ref(v___y_4190_);
return v_res_4194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__2(lean_object* v_as_4195_, size_t v_i_4196_, size_t v_stop_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_){
_start:
{
uint8_t v___x_4205_; 
v___x_4205_ = lean_usize_dec_eq(v_i_4196_, v_stop_4197_);
if (v___x_4205_ == 0)
{
uint8_t v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; 
v___x_4206_ = 1;
v___x_4207_ = lean_array_uget_borrowed(v_as_4195_, v_i_4196_);
lean_inc(v___x_4207_);
v___x_4208_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1___redArg(v___x_4207_, v___y_4199_);
if (lean_obj_tag(v___x_4208_) == 0)
{
lean_object* v_a_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4218_; 
v_a_4209_ = lean_ctor_get(v___x_4208_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4208_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4211_ = v___x_4208_;
v_isShared_4212_ = v_isSharedCheck_4218_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_a_4209_);
lean_dec(v___x_4208_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4218_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
uint8_t v___x_4213_; 
v___x_4213_ = lean_unbox(v_a_4209_);
lean_dec(v_a_4209_);
if (v___x_4213_ == 0)
{
lean_object* v___x_4214_; lean_object* v___x_4216_; 
v___x_4214_ = lean_box(v___x_4206_);
if (v_isShared_4212_ == 0)
{
lean_ctor_set(v___x_4211_, 0, v___x_4214_);
v___x_4216_ = v___x_4211_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v___x_4214_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
else
{
lean_del_object(v___x_4211_);
goto v___jp_4201_;
}
}
}
else
{
if (lean_obj_tag(v___x_4208_) == 0)
{
lean_object* v_a_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4228_; 
v_a_4219_ = lean_ctor_get(v___x_4208_, 0);
v_isSharedCheck_4228_ = !lean_is_exclusive(v___x_4208_);
if (v_isSharedCheck_4228_ == 0)
{
v___x_4221_ = v___x_4208_;
v_isShared_4222_ = v_isSharedCheck_4228_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_a_4219_);
lean_dec(v___x_4208_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4228_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
uint8_t v___x_4223_; 
v___x_4223_ = lean_unbox(v_a_4219_);
lean_dec(v_a_4219_);
if (v___x_4223_ == 0)
{
lean_del_object(v___x_4221_);
goto v___jp_4201_;
}
else
{
lean_object* v___x_4224_; lean_object* v___x_4226_; 
v___x_4224_ = lean_box(v___x_4206_);
if (v_isShared_4222_ == 0)
{
lean_ctor_set_tag(v___x_4221_, 0);
lean_ctor_set(v___x_4221_, 0, v___x_4224_);
v___x_4226_ = v___x_4221_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v___x_4224_);
v___x_4226_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
return v___x_4226_;
}
}
}
}
else
{
return v___x_4208_;
}
}
}
else
{
uint8_t v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; 
v___x_4229_ = 0;
v___x_4230_ = lean_box(v___x_4229_);
v___x_4231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4231_, 0, v___x_4230_);
return v___x_4231_;
}
v___jp_4201_:
{
size_t v___x_4202_; size_t v___x_4203_; 
v___x_4202_ = ((size_t)1ULL);
v___x_4203_ = lean_usize_add(v_i_4196_, v___x_4202_);
v_i_4196_ = v___x_4203_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__2___boxed(lean_object* v_as_4232_, lean_object* v_i_4233_, lean_object* v_stop_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_){
_start:
{
size_t v_i_boxed_4238_; size_t v_stop_boxed_4239_; lean_object* v_res_4240_; 
v_i_boxed_4238_ = lean_unbox_usize(v_i_4233_);
lean_dec(v_i_4233_);
v_stop_boxed_4239_ = lean_unbox_usize(v_stop_4234_);
lean_dec(v_stop_4234_);
v_res_4240_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__2(v_as_4232_, v_i_boxed_4238_, v_stop_boxed_4239_, v___y_4235_, v___y_4236_);
lean_dec(v___y_4236_);
lean_dec_ref(v___y_4235_);
lean_dec_ref(v_as_4232_);
return v_res_4240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__0(lean_object* v_as_4241_, size_t v_sz_4242_, size_t v_i_4243_, lean_object* v_b_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_){
_start:
{
uint8_t v___x_4248_; 
v___x_4248_ = lean_usize_dec_lt(v_i_4243_, v_sz_4242_);
if (v___x_4248_ == 0)
{
lean_object* v___x_4249_; 
v___x_4249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4249_, 0, v_b_4244_);
return v___x_4249_;
}
else
{
lean_object* v_a_4250_; lean_object* v___x_4251_; 
v_a_4250_ = lean_array_uget_borrowed(v_as_4241_, v_i_4243_);
lean_inc(v_a_4250_);
v___x_4251_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance(v_a_4250_, v___y_4245_, v___y_4246_);
if (lean_obj_tag(v___x_4251_) == 0)
{
lean_object* v___x_4252_; size_t v___x_4253_; size_t v___x_4254_; 
lean_dec_ref_known(v___x_4251_, 1);
v___x_4252_ = lean_box(0);
v___x_4253_ = ((size_t)1ULL);
v___x_4254_ = lean_usize_add(v_i_4243_, v___x_4253_);
v_i_4243_ = v___x_4254_;
v_b_4244_ = v___x_4252_;
goto _start;
}
else
{
return v___x_4251_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__0___boxed(lean_object* v_as_4256_, lean_object* v_sz_4257_, lean_object* v_i_4258_, lean_object* v_b_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_){
_start:
{
size_t v_sz_boxed_4263_; size_t v_i_boxed_4264_; lean_object* v_res_4265_; 
v_sz_boxed_4263_ = lean_unbox_usize(v_sz_4257_);
lean_dec(v_sz_4257_);
v_i_boxed_4264_ = lean_unbox_usize(v_i_4258_);
lean_dec(v_i_4258_);
v_res_4265_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__0(v_as_4256_, v_sz_boxed_4263_, v_i_boxed_4264_, v_b_4259_, v___y_4260_, v___y_4261_);
lean_dec(v___y_4261_);
lean_dec_ref(v___y_4260_);
lean_dec_ref(v_as_4256_);
return v_res_4265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler(lean_object* v_declNames_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_){
_start:
{
lean_object* v___y_4294_; lean_object* v___x_4297_; lean_object* v___x_4298_; uint8_t v___x_4299_; 
v___x_4297_ = lean_unsigned_to_nat(0u);
v___x_4298_ = lean_array_get_size(v_declNames_4266_);
v___x_4299_ = lean_nat_dec_lt(v___x_4297_, v___x_4298_);
if (v___x_4299_ == 0)
{
lean_object* v___x_4300_; 
v___x_4300_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___lam__0(v___x_4299_, v_a_4267_, v_a_4268_);
v___y_4294_ = v___x_4300_;
goto v___jp_4293_;
}
else
{
if (v___x_4299_ == 0)
{
goto v___jp_4270_;
}
else
{
size_t v___x_4301_; size_t v___x_4302_; lean_object* v___x_4303_; 
v___x_4301_ = ((size_t)0ULL);
v___x_4302_ = lean_usize_of_nat(v___x_4298_);
v___x_4303_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__2(v_declNames_4266_, v___x_4301_, v___x_4302_, v_a_4267_, v_a_4268_);
if (lean_obj_tag(v___x_4303_) == 0)
{
lean_object* v_a_4304_; uint8_t v___x_4305_; lean_object* v___x_4306_; 
v_a_4304_ = lean_ctor_get(v___x_4303_, 0);
lean_inc(v_a_4304_);
lean_dec_ref_known(v___x_4303_, 1);
v___x_4305_ = lean_unbox(v_a_4304_);
lean_dec(v_a_4304_);
v___x_4306_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___lam__0(v___x_4305_, v_a_4267_, v_a_4268_);
v___y_4294_ = v___x_4306_;
goto v___jp_4293_;
}
else
{
v___y_4294_ = v___x_4303_;
goto v___jp_4293_;
}
}
}
v___jp_4270_:
{
lean_object* v___x_4271_; size_t v_sz_4272_; size_t v___x_4273_; lean_object* v___x_4274_; 
v___x_4271_ = lean_box(0);
v_sz_4272_ = lean_array_size(v_declNames_4266_);
v___x_4273_ = ((size_t)0ULL);
v___x_4274_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__0(v_declNames_4266_, v_sz_4272_, v___x_4273_, v___x_4271_, v_a_4267_, v_a_4268_);
if (lean_obj_tag(v___x_4274_) == 0)
{
lean_object* v___x_4276_; uint8_t v_isShared_4277_; uint8_t v_isSharedCheck_4283_; 
v_isSharedCheck_4283_ = !lean_is_exclusive(v___x_4274_);
if (v_isSharedCheck_4283_ == 0)
{
lean_object* v_unused_4284_; 
v_unused_4284_ = lean_ctor_get(v___x_4274_, 0);
lean_dec(v_unused_4284_);
v___x_4276_ = v___x_4274_;
v_isShared_4277_ = v_isSharedCheck_4283_;
goto v_resetjp_4275_;
}
else
{
lean_dec(v___x_4274_);
v___x_4276_ = lean_box(0);
v_isShared_4277_ = v_isSharedCheck_4283_;
goto v_resetjp_4275_;
}
v_resetjp_4275_:
{
uint8_t v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4281_; 
v___x_4278_ = 1;
v___x_4279_ = lean_box(v___x_4278_);
if (v_isShared_4277_ == 0)
{
lean_ctor_set(v___x_4276_, 0, v___x_4279_);
v___x_4281_ = v___x_4276_;
goto v_reusejp_4280_;
}
else
{
lean_object* v_reuseFailAlloc_4282_; 
v_reuseFailAlloc_4282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4282_, 0, v___x_4279_);
v___x_4281_ = v_reuseFailAlloc_4282_;
goto v_reusejp_4280_;
}
v_reusejp_4280_:
{
return v___x_4281_;
}
}
}
else
{
lean_object* v_a_4285_; lean_object* v___x_4287_; uint8_t v_isShared_4288_; uint8_t v_isSharedCheck_4292_; 
v_a_4285_ = lean_ctor_get(v___x_4274_, 0);
v_isSharedCheck_4292_ = !lean_is_exclusive(v___x_4274_);
if (v_isSharedCheck_4292_ == 0)
{
v___x_4287_ = v___x_4274_;
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
else
{
lean_inc(v_a_4285_);
lean_dec(v___x_4274_);
v___x_4287_ = lean_box(0);
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
v_resetjp_4286_:
{
lean_object* v___x_4290_; 
if (v_isShared_4288_ == 0)
{
v___x_4290_ = v___x_4287_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4291_; 
v_reuseFailAlloc_4291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4291_, 0, v_a_4285_);
v___x_4290_ = v_reuseFailAlloc_4291_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
return v___x_4290_;
}
}
}
}
v___jp_4293_:
{
if (lean_obj_tag(v___y_4294_) == 0)
{
lean_object* v_a_4295_; uint8_t v___x_4296_; 
v_a_4295_ = lean_ctor_get(v___y_4294_, 0);
v___x_4296_ = lean_unbox(v_a_4295_);
if (v___x_4296_ == 0)
{
return v___y_4294_;
}
else
{
lean_dec_ref_known(v___y_4294_, 1);
goto v___jp_4270_;
}
}
else
{
return v___y_4294_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___boxed(lean_object* v_declNames_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_){
_start:
{
lean_object* v_res_4311_; 
v_res_4311_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler(v_declNames_4307_, v_a_4308_, v_a_4309_);
lean_dec(v_a_4309_);
lean_dec_ref(v_a_4308_);
lean_dec_ref(v_declNames_4307_);
return v_res_4311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; 
v___x_4360_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader___closed__0));
v___x_4361_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__0_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_));
v___x_4362_ = l_Lean_Elab_registerDerivingHandler(v___x_4360_, v___x_4361_);
if (lean_obj_tag(v___x_4362_) == 0)
{
lean_object* v___x_4363_; uint8_t v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; 
lean_dec_ref_known(v___x_4362_, 1);
v___x_4363_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__0));
v___x_4364_ = 0;
v___x_4365_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__18_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_));
v___x_4366_ = l_Lean_registerTraceClass(v___x_4363_, v___x_4364_, v___x_4365_);
return v___x_4366_;
}
else
{
return v___x_4362_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2____boxed(lean_object* v_a_4367_){
_start:
{
lean_object* v_res_4368_; 
v_res_4368_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_();
return v_res_4368_;
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
