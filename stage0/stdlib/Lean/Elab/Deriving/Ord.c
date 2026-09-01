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
lean_object* v_toCold_312_; lean_object* v_ref_313_; lean_object* v_currMacroScope_314_; lean_object* v_quotContext_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v_toCold_312_ = lean_ctor_get(v___y_309_, 0);
v_ref_313_ = lean_ctor_get(v___y_309_, 4);
v_currMacroScope_314_ = lean_ctor_get(v___y_309_, 9);
v_quotContext_315_ = lean_ctor_get(v_toCold_312_, 2);
v___x_316_ = l_Lean_SourceInfo_fromRef(v_ref_313_, v___x_300_);
v___x_317_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3));
v___x_318_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__5);
v___x_319_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__8));
lean_inc_n(v_currMacroScope_314_, 3);
lean_inc_n(v_quotContext_315_, 3);
v___x_320_ = l_Lean_addMacroScope(v_quotContext_315_, v___x_319_, v_currMacroScope_314_);
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
v___x_331_ = l_Lean_addMacroScope(v_quotContext_315_, v___x_330_, v_currMacroScope_314_);
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
v___x_338_ = l_Lean_addMacroScope(v_quotContext_315_, v___x_337_, v_currMacroScope_314_);
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
uint8_t v___x_48982__boxed_361_; lean_object* v_res_362_; 
v___x_48982__boxed_361_ = lean_unbox(v___x_349_);
v_res_362_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0(v___x_48982__boxed_361_, v___x_350_, v___x_351_, v_snd_352_, v_rhs_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
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
v_ref_456_ = lean_ctor_get(v___y_391_, 4);
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
v_ref_494_ = lean_ctor_get(v___y_391_, 4);
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
v_ref_539_ = lean_ctor_get(v___y_535_, 4);
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
v_ref_568_ = lean_ctor_get(v___y_559_, 4);
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
lean_object* v_a_697_; lean_object* v_toCold_698_; lean_object* v_ref_699_; lean_object* v_currMacroScope_700_; lean_object* v___x_701_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_a_697_);
lean_dec_ref_known(v___x_696_, 1);
v_toCold_698_ = lean_ctor_get(v___y_676_, 0);
v_ref_699_ = lean_ctor_get(v___y_676_, 4);
v_currMacroScope_700_ = lean_ctor_get(v___y_676_, 9);
lean_inc_ref(v___f_668_);
lean_inc(v___y_677_);
lean_inc_ref(v___y_676_);
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
lean_inc(v___y_673_);
lean_inc_ref(v___y_672_);
v___x_701_ = lean_apply_7(v___f_668_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, lean_box(0));
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; lean_object* v___x_703_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_a_702_);
lean_dec_ref_known(v___x_701_, 1);
lean_inc_ref(v___f_668_);
lean_inc(v___y_677_);
lean_inc_ref(v___y_676_);
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
lean_inc(v___y_673_);
lean_inc_ref(v___y_672_);
v___x_703_ = lean_apply_7(v___f_668_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, lean_box(0));
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_a_704_; lean_object* v___x_705_; 
v_a_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_a_704_);
lean_dec_ref_known(v___x_703_, 1);
lean_inc_ref(v___f_668_);
lean_inc(v___y_677_);
lean_inc_ref(v___y_676_);
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
lean_inc(v___y_673_);
lean_inc_ref(v___y_672_);
v___x_705_ = lean_apply_7(v___f_668_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, lean_box(0));
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v___x_707_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_a_706_);
lean_dec_ref_known(v___x_705_, 1);
lean_inc_ref(v___f_668_);
lean_inc(v___y_677_);
lean_inc_ref(v___y_676_);
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
lean_inc(v___y_673_);
lean_inc_ref(v___y_672_);
v___x_707_ = lean_apply_7(v___f_668_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, lean_box(0));
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_snd_708_; lean_object* v_a_709_; lean_object* v_fst_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_858_; 
v_snd_708_ = lean_ctor_get(v_a_697_, 1);
lean_inc(v_snd_708_);
v_a_709_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_709_);
lean_dec_ref_known(v___x_707_, 1);
v_fst_710_ = lean_ctor_get(v_a_697_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v_a_697_);
if (v_isSharedCheck_858_ == 0)
{
lean_object* v_unused_859_; 
v_unused_859_ = lean_ctor_get(v_a_697_, 1);
lean_dec(v_unused_859_);
v___x_712_ = v_a_697_;
v_isShared_713_ = v_isSharedCheck_858_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_fst_710_);
lean_dec(v_a_697_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_858_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v_fst_714_; lean_object* v_snd_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_857_; 
v_fst_714_ = lean_ctor_get(v_snd_708_, 0);
v_snd_715_ = lean_ctor_get(v_snd_708_, 1);
v_isSharedCheck_857_ = !lean_is_exclusive(v_snd_708_);
if (v_isSharedCheck_857_ == 0)
{
v___x_717_ = v_snd_708_;
v_isShared_718_ = v_isSharedCheck_857_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_snd_715_);
lean_inc(v_fst_714_);
lean_dec(v_snd_708_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_857_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v_quotContext_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v_quotContext_719_ = lean_ctor_get(v_toCold_698_, 2);
v___x_720_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1);
v___x_721_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3));
lean_inc(v_currMacroScope_700_);
lean_inc(v_quotContext_719_);
v___x_722_ = l_Lean_addMacroScope(v_quotContext_719_, v___x_721_, v_currMacroScope_700_);
v___x_723_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__7));
v___x_724_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_724_, 0, v_a_709_);
lean_ctor_set(v___x_724_, 1, v___x_720_);
lean_ctor_set(v___x_724_, 2, v___x_722_);
lean_ctor_set(v___x_724_, 3, v___x_723_);
lean_inc(v___y_677_);
lean_inc_ref(v___y_676_);
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
lean_inc(v___y_673_);
lean_inc_ref(v___y_672_);
v___x_725_ = lean_apply_8(v_snd_715_, v___x_724_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, lean_box(0));
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
if (v_isShared_718_ == 0)
{
lean_ctor_set_tag(v___x_717_, 2);
lean_ctor_set(v___x_717_, 1, v___x_738_);
lean_ctor_set(v___x_717_, 0, v___x_737_);
v___x_740_ = v___x_717_;
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
lean_inc(v_a_702_);
if (v_isShared_713_ == 0)
{
lean_ctor_set_tag(v___x_712_, 2);
lean_ctor_set(v___x_712_, 1, v___x_738_);
lean_ctor_set(v___x_712_, 0, v_a_702_);
v___x_744_ = v___x_712_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_702_);
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
lean_inc_n(v_a_702_, 2);
v___x_747_ = l_Lean_Syntax_node2(v_a_702_, v___x_745_, v___x_744_, v___x_742_);
v___x_748_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_749_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11);
v___x_750_ = l_Array_append___redArg(v___x_749_, v_fst_710_);
lean_dec(v_fst_710_);
v___x_751_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_751_, 0, v___x_737_);
lean_ctor_set(v___x_751_, 1, v___x_748_);
lean_ctor_set(v___x_751_, 2, v___x_750_);
v___x_752_ = l_Array_append___redArg(v___x_749_, v_fst_714_);
lean_dec(v_fst_714_);
v___x_753_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_753_, 0, v_a_702_);
lean_ctor_set(v___x_753_, 1, v___x_748_);
lean_ctor_set(v___x_753_, 2, v___x_752_);
v___x_754_ = l_Lean_Syntax_node2(v___x_737_, v___x_741_, v___x_746_, v___x_751_);
v___x_755_ = l_Lean_Syntax_node2(v_a_702_, v___x_741_, v___x_747_, v___x_753_);
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
lean_inc(v_a_704_);
v___x_762_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_762_, 0, v_a_704_);
lean_ctor_set(v___x_762_, 1, v___x_761_);
v___x_763_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8));
v___x_764_ = l_Lean_Syntax_node1(v_a_704_, v___x_763_, v___x_762_);
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
lean_inc_n(v_currMacroScope_700_, 2);
lean_inc_n(v_quotContext_719_, 2);
v___x_784_ = l_Lean_addMacroScope(v_quotContext_719_, v___x_783_, v_currMacroScope_700_);
v___x_785_ = l_Lean_Syntax_node1(v_a_728_, v___x_748_, v___x_781_);
v___x_786_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__17));
v___x_787_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_787_, 0, v_a_730_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
lean_inc(v_a_706_);
v___x_788_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_788_, 0, v_a_706_);
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
v___x_793_ = l_Lean_Syntax_node1(v_a_706_, v___x_763_, v___x_788_);
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
v___x_810_ = l_Lean_addMacroScope(v_quotContext_719_, v___x_809_, v_currMacroScope_700_);
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
lean_del_object(v___x_717_);
lean_dec(v_fst_714_);
lean_del_object(v___x_712_);
lean_dec(v_fst_710_);
lean_dec(v_a_706_);
lean_dec(v_a_704_);
lean_dec(v_a_702_);
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
lean_del_object(v___x_717_);
lean_dec(v_fst_714_);
lean_del_object(v___x_712_);
lean_dec(v_fst_710_);
lean_dec(v_a_706_);
lean_dec(v_a_704_);
lean_dec(v_a_702_);
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
lean_del_object(v___x_717_);
lean_dec(v_fst_714_);
lean_del_object(v___x_712_);
lean_dec(v_fst_710_);
lean_dec(v_a_706_);
lean_dec(v_a_704_);
lean_dec(v_a_702_);
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
lean_del_object(v___x_717_);
lean_dec(v_fst_714_);
lean_del_object(v___x_712_);
lean_dec(v_fst_710_);
lean_dec(v_a_706_);
lean_dec(v_a_704_);
lean_dec(v_a_702_);
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
lean_dec(v_a_706_);
lean_dec(v_a_704_);
lean_dec(v_a_702_);
lean_dec(v_a_697_);
lean_dec(v_a_684_);
lean_dec(v_head_669_);
lean_dec_ref(v___f_668_);
v_a_860_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_707_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_707_);
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
lean_dec(v_a_704_);
lean_dec(v_a_702_);
lean_dec(v_a_697_);
lean_dec(v_a_684_);
lean_dec(v_head_669_);
lean_dec_ref(v___f_668_);
v_a_868_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_705_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_705_);
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
lean_dec(v_a_702_);
lean_dec(v_a_697_);
lean_dec(v_a_684_);
lean_dec(v_head_669_);
lean_dec_ref(v___f_668_);
v_a_876_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_703_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_703_);
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
v_a_884_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_701_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_701_);
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
v_ref_942_ = lean_ctor_get(v___y_939_, 4);
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
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_46245__overap_1062_; lean_object* v___x_1063_; 
v___x_1060_ = lean_box(0);
v___x_1061_ = l_instInhabitedOfMonad___redArg(v___x_1059_, v___x_1060_);
v___x_46245__overap_1062_ = lean_panic_fn_borrowed(v___x_1061_, v_msg_979_);
lean_dec(v___x_1061_);
lean_inc(v___y_985_);
lean_inc_ref(v___y_984_);
lean_inc(v___y_983_);
lean_inc_ref(v___y_982_);
lean_inc(v___y_981_);
lean_inc_ref(v___y_980_);
v___x_1063_ = lean_apply_7(v___x_46245__overap_1062_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, lean_box(0));
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
lean_object* v___x_1097_; lean_object* v_env_1098_; lean_object* v___x_1099_; lean_object* v_mctx_1100_; lean_object* v_lctx_1101_; lean_object* v_options_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1097_ = lean_st_ref_get(v___y_1095_);
v_env_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc_ref(v_env_1098_);
lean_dec(v___x_1097_);
v___x_1099_ = lean_st_ref_get(v___y_1093_);
v_mctx_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc_ref(v_mctx_1100_);
lean_dec(v___x_1099_);
v_lctx_1101_ = lean_ctor_get(v___y_1092_, 2);
v_options_1102_ = lean_ctor_get(v___y_1094_, 1);
lean_inc_ref(v_options_1102_);
lean_inc_ref(v_lctx_1101_);
v___x_1103_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1103_, 0, v_env_1098_);
lean_ctor_set(v___x_1103_, 1, v_mctx_1100_);
lean_ctor_set(v___x_1103_, 2, v_lctx_1101_);
lean_ctor_set(v___x_1103_, 3, v_options_1102_);
v___x_1104_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1103_);
lean_ctor_set(v___x_1104_, 1, v_msgData_1091_);
v___x_1105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__2___boxed(lean_object* v_msgData_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(v_msgData_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
return v_res_1112_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = lean_box(1);
v___x_1114_ = l_Lean_MessageData_ofFormat(v___x_1113_);
return v___x_1114_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__2));
v___x_1119_ = l_Lean_MessageData_ofFormat(v___x_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12(lean_object* v_x_1120_, lean_object* v_x_1121_){
_start:
{
if (lean_obj_tag(v_x_1121_) == 0)
{
return v_x_1120_;
}
else
{
lean_object* v_head_1122_; lean_object* v_tail_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1145_; 
v_head_1122_ = lean_ctor_get(v_x_1121_, 0);
v_tail_1123_ = lean_ctor_get(v_x_1121_, 1);
v_isSharedCheck_1145_ = !lean_is_exclusive(v_x_1121_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1125_ = v_x_1121_;
v_isShared_1126_ = v_isSharedCheck_1145_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_tail_1123_);
lean_inc(v_head_1122_);
lean_dec(v_x_1121_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1145_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v_before_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1143_; 
v_before_1127_ = lean_ctor_get(v_head_1122_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v_head_1122_);
if (v_isSharedCheck_1143_ == 0)
{
lean_object* v_unused_1144_; 
v_unused_1144_ = lean_ctor_get(v_head_1122_, 1);
lean_dec(v_unused_1144_);
v___x_1129_ = v_head_1122_;
v_isShared_1130_ = v_isSharedCheck_1143_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_before_1127_);
lean_dec(v_head_1122_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1143_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1131_; lean_object* v___x_1133_; 
v___x_1131_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0);
if (v_isShared_1130_ == 0)
{
lean_ctor_set_tag(v___x_1129_, 7);
lean_ctor_set(v___x_1129_, 1, v___x_1131_);
lean_ctor_set(v___x_1129_, 0, v_x_1120_);
v___x_1133_ = v___x_1129_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_x_1120_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1134_; lean_object* v___x_1136_; 
v___x_1134_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__3);
if (v_isShared_1126_ == 0)
{
lean_ctor_set_tag(v___x_1125_, 7);
lean_ctor_set(v___x_1125_, 1, v___x_1134_);
lean_ctor_set(v___x_1125_, 0, v___x_1133_);
v___x_1136_ = v___x_1125_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1133_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1137_ = l_Lean_MessageData_ofSyntax(v_before_1127_);
v___x_1138_ = l_Lean_indentD(v___x_1137_);
v___x_1139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1136_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v_x_1120_ = v___x_1139_;
v_x_1121_ = v_tail_1123_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(lean_object* v_opts_1146_, lean_object* v_opt_1147_){
_start:
{
lean_object* v_name_1148_; lean_object* v_defValue_1149_; lean_object* v_map_1150_; lean_object* v___x_1151_; 
v_name_1148_ = lean_ctor_get(v_opt_1147_, 0);
v_defValue_1149_ = lean_ctor_get(v_opt_1147_, 1);
v_map_1150_ = lean_ctor_get(v_opts_1146_, 0);
v___x_1151_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1150_, v_name_1148_);
if (lean_obj_tag(v___x_1151_) == 0)
{
uint8_t v___x_1152_; 
v___x_1152_ = lean_unbox(v_defValue_1149_);
return v___x_1152_;
}
else
{
lean_object* v_val_1153_; 
v_val_1153_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_val_1153_);
lean_dec_ref_known(v___x_1151_, 1);
if (lean_obj_tag(v_val_1153_) == 1)
{
uint8_t v_v_1154_; 
v_v_1154_ = lean_ctor_get_uint8(v_val_1153_, 0);
lean_dec_ref_known(v_val_1153_, 0);
return v_v_1154_;
}
else
{
uint8_t v___x_1155_; 
lean_dec(v_val_1153_);
v___x_1155_ = lean_unbox(v_defValue_1149_);
return v___x_1155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11___boxed(lean_object* v_opts_1156_, lean_object* v_opt_1157_){
_start:
{
uint8_t v_res_1158_; lean_object* v_r_1159_; 
v_res_1158_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(v_opts_1156_, v_opt_1157_);
lean_dec_ref(v_opt_1157_);
lean_dec_ref(v_opts_1156_);
v_r_1159_ = lean_box(v_res_1158_);
return v_r_1159_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__1));
v___x_1164_ = l_Lean_MessageData_ofFormat(v___x_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(lean_object* v_msgData_1165_, lean_object* v_macroStack_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v_options_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; 
v_options_1169_ = lean_ctor_get(v___y_1167_, 1);
v___x_1170_ = l_Lean_Elab_pp_macroStack;
v___x_1171_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(v_options_1169_, v___x_1170_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; 
lean_dec(v_macroStack_1166_);
v___x_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1172_, 0, v_msgData_1165_);
return v___x_1172_;
}
else
{
if (lean_obj_tag(v_macroStack_1166_) == 0)
{
lean_object* v___x_1173_; 
v___x_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1173_, 0, v_msgData_1165_);
return v___x_1173_;
}
else
{
lean_object* v_head_1174_; lean_object* v_after_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1190_; 
v_head_1174_ = lean_ctor_get(v_macroStack_1166_, 0);
lean_inc(v_head_1174_);
v_after_1175_ = lean_ctor_get(v_head_1174_, 1);
v_isSharedCheck_1190_ = !lean_is_exclusive(v_head_1174_);
if (v_isSharedCheck_1190_ == 0)
{
lean_object* v_unused_1191_; 
v_unused_1191_ = lean_ctor_get(v_head_1174_, 0);
lean_dec(v_unused_1191_);
v___x_1177_ = v_head_1174_;
v_isShared_1178_ = v_isSharedCheck_1190_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_after_1175_);
lean_dec(v_head_1174_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1190_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1179_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0);
if (v_isShared_1178_ == 0)
{
lean_ctor_set_tag(v___x_1177_, 7);
lean_ctor_set(v___x_1177_, 1, v___x_1179_);
lean_ctor_set(v___x_1177_, 0, v_msgData_1165_);
v___x_1181_ = v___x_1177_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_msgData_1165_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v___x_1179_);
v___x_1181_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v_msgData_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1182_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_1183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1181_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = l_Lean_MessageData_ofSyntax(v_after_1175_);
v___x_1185_ = l_Lean_indentD(v___x_1184_);
v_msgData_1186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_1186_, 0, v___x_1183_);
lean_ctor_set(v_msgData_1186_, 1, v___x_1185_);
v___x_1187_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12(v_msgData_1186_, v_macroStack_1166_);
v___x_1188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1187_);
return v___x_1188_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_msgData_1192_, lean_object* v_macroStack_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(v_msgData_1192_, v_macroStack_1193_, v___y_1194_);
lean_dec_ref(v___y_1194_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0___redArg(lean_object* v_msg_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v_ref_1205_; lean_object* v___x_1206_; lean_object* v_a_1207_; lean_object* v_macroStack_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1219_; 
v_ref_1205_ = lean_ctor_get(v___y_1202_, 4);
v___x_1206_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(v_msg_1197_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_a_1207_);
lean_dec_ref(v___x_1206_);
v_macroStack_1208_ = lean_ctor_get(v___y_1198_, 1);
v___x_1209_ = l_Lean_Elab_getBetterRef(v_ref_1205_, v_macroStack_1208_);
lean_inc(v_macroStack_1208_);
v___x_1210_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(v_a_1207_, v_macroStack_1208_, v___y_1202_);
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1213_ = v___x_1210_;
v_isShared_1214_ = v_isSharedCheck_1219_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1210_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1219_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1215_; lean_object* v___x_1217_; 
v___x_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1209_);
lean_ctor_set(v___x_1215_, 1, v_a_1211_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set_tag(v___x_1213_, 1);
lean_ctor_set(v___x_1213_, 0, v___x_1215_);
v___x_1217_ = v___x_1213_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1215_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0___redArg(v_msg_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
return v_res_1228_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__0));
v___x_1231_ = l_Lean_stringToMessageData(v___x_1230_);
return v___x_1231_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1233_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__2));
v___x_1234_ = l_Lean_stringToMessageData(v___x_1233_);
return v___x_1234_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__7(void){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1238_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__6));
v___x_1239_ = lean_unsigned_to_nat(11u);
v___x_1240_ = lean_unsigned_to_nat(122u);
v___x_1241_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__5));
v___x_1242_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__4));
v___x_1243_ = l_mkPanicMessageWithDecl(v___x_1242_, v___x_1241_, v___x_1240_, v___x_1239_, v___x_1238_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0(lean_object* v_constName_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v___x_1260_; lean_object* v_env_1261_; uint8_t v___x_1262_; lean_object* v___x_1263_; 
v___x_1260_ = lean_st_ref_get(v___y_1250_);
v_env_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc_ref(v_env_1261_);
lean_dec(v___x_1260_);
v___x_1262_ = 0;
lean_inc(v_constName_1244_);
v___x_1263_ = l_Lean_Environment_findAsync_x3f(v_env_1261_, v_constName_1244_, v___x_1262_);
if (lean_obj_tag(v___x_1263_) == 1)
{
lean_object* v_val_1264_; uint8_t v_kind_1265_; 
v_val_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_val_1264_);
lean_dec_ref_known(v___x_1263_, 1);
v_kind_1265_ = lean_ctor_get_uint8(v_val_1264_, sizeof(void*)*3);
if (v_kind_1265_ == 6)
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1264_);
if (lean_obj_tag(v___x_1266_) == 6)
{
lean_object* v_val_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
lean_dec(v_constName_1244_);
v_val_1267_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v___x_1266_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_val_1267_);
lean_dec(v___x_1266_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
lean_ctor_set_tag(v___x_1269_, 0);
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_val_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
else
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
lean_dec_ref(v___x_1266_);
v___x_1275_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__7);
v___x_1276_ = l_panic___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__1(v___x_1275_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1285_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1279_ = v___x_1276_;
v_isShared_1280_ = v_isSharedCheck_1285_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1276_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1285_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
if (lean_obj_tag(v_a_1277_) == 0)
{
lean_del_object(v___x_1279_);
goto v___jp_1252_;
}
else
{
lean_object* v_val_1281_; lean_object* v___x_1283_; 
lean_dec(v_constName_1244_);
v_val_1281_ = lean_ctor_get(v_a_1277_, 0);
lean_inc(v_val_1281_);
lean_dec_ref_known(v_a_1277_, 1);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 0, v_val_1281_);
v___x_1283_ = v___x_1279_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_val_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_dec(v_constName_1244_);
v_a_1286_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1276_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1276_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
else
{
lean_dec(v_val_1264_);
goto v___jp_1252_;
}
}
else
{
lean_dec(v___x_1263_);
goto v___jp_1252_;
}
v___jp_1252_:
{
lean_object* v___x_1253_; uint8_t v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1253_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1);
v___x_1254_ = 0;
v___x_1255_ = l_Lean_MessageData_ofConstName(v_constName_1244_, v___x_1254_);
v___x_1256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1253_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
v___x_1257_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__3);
v___x_1258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1256_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
v___x_1259_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0___redArg(v___x_1258_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
return v___x_1259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___boxed(lean_object* v_constName_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0(v_constName_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
lean_dec(v___y_1300_);
lean_dec_ref(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__6(size_t v_sz_1303_, size_t v_i_1304_, lean_object* v_bs_1305_){
_start:
{
uint8_t v___x_1306_; 
v___x_1306_ = lean_usize_dec_lt(v_i_1304_, v_sz_1303_);
if (v___x_1306_ == 0)
{
return v_bs_1305_;
}
else
{
lean_object* v_v_1307_; lean_object* v___x_1308_; lean_object* v_bs_x27_1309_; size_t v___x_1310_; size_t v___x_1311_; lean_object* v___x_1312_; 
v_v_1307_ = lean_array_uget(v_bs_1305_, v_i_1304_);
v___x_1308_ = lean_unsigned_to_nat(0u);
v_bs_x27_1309_ = lean_array_uset(v_bs_1305_, v_i_1304_, v___x_1308_);
v___x_1310_ = ((size_t)1ULL);
v___x_1311_ = lean_usize_add(v_i_1304_, v___x_1310_);
v___x_1312_ = lean_array_uset(v_bs_x27_1309_, v_i_1304_, v_v_1307_);
v_i_1304_ = v___x_1311_;
v_bs_1305_ = v___x_1312_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__6___boxed(lean_object* v_sz_1314_, lean_object* v_i_1315_, lean_object* v_bs_1316_){
_start:
{
size_t v_sz_boxed_1317_; size_t v_i_boxed_1318_; lean_object* v_res_1319_; 
v_sz_boxed_1317_ = lean_unbox_usize(v_sz_1314_);
lean_dec(v_sz_1314_);
v_i_boxed_1318_ = lean_unbox_usize(v_i_1315_);
lean_dec(v_i_1315_);
v_res_1319_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__6(v_sz_boxed_1317_, v_i_boxed_1318_, v_bs_1316_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg(lean_object* v_indVal_1324_, lean_object* v_as_x27_1325_, lean_object* v_b_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
if (lean_obj_tag(v_as_x27_1325_) == 0)
{
lean_object* v___x_1334_; 
lean_dec_ref(v_indVal_1324_);
v___x_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1334_, 0, v_b_1326_);
return v___x_1334_;
}
else
{
lean_object* v_head_1335_; lean_object* v_tail_1336_; lean_object* v___x_1337_; 
v_head_1335_ = lean_ctor_get(v_as_x27_1325_, 0);
v_tail_1336_ = lean_ctor_get(v_as_x27_1325_, 1);
lean_inc(v_head_1335_);
v___x_1337_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0(v_head_1335_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v_a_1338_; lean_object* v_toConstantVal_1339_; lean_object* v_numFields_1340_; lean_object* v_type_1341_; lean_object* v___f_1342_; lean_object* v___f_1343_; lean_object* v___x_1344_; lean_object* v_alts_1345_; lean_object* v___f_1346_; uint8_t v___x_1347_; lean_object* v___x_1348_; 
v_a_1338_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_a_1338_);
lean_dec_ref_known(v___x_1337_, 1);
v_toConstantVal_1339_ = lean_ctor_get(v_a_1338_, 0);
lean_inc_ref(v_toConstantVal_1339_);
v_numFields_1340_ = lean_ctor_get(v_a_1338_, 4);
lean_inc(v_numFields_1340_);
lean_dec(v_a_1338_);
v_type_1341_ = lean_ctor_get(v_toConstantVal_1339_, 2);
lean_inc_ref(v_type_1341_);
lean_dec_ref(v_toConstantVal_1339_);
v___f_1342_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__0));
v___f_1343_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__1));
v___x_1344_ = lean_unsigned_to_nat(0u);
v_alts_1345_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__2));
lean_inc(v_head_1335_);
lean_inc_ref(v_indVal_1324_);
v___f_1346_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___boxed), 16, 7);
lean_closure_set(v___f_1346_, 0, v_indVal_1324_);
lean_closure_set(v___f_1346_, 1, v___x_1344_);
lean_closure_set(v___f_1346_, 2, v_alts_1345_);
lean_closure_set(v___f_1346_, 3, v___f_1342_);
lean_closure_set(v___f_1346_, 4, v_numFields_1340_);
lean_closure_set(v___f_1346_, 5, v___f_1343_);
lean_closure_set(v___f_1346_, 6, v_head_1335_);
v___x_1347_ = 0;
v___x_1348_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg(v_type_1341_, v___f_1346_, v___x_1347_, v___x_1347_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; size_t v_sz_1350_; size_t v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_a_1349_);
lean_dec_ref_known(v___x_1348_, 1);
v_sz_1350_ = lean_array_size(v_a_1349_);
v___x_1351_ = ((size_t)0ULL);
v___x_1352_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__6(v_sz_1350_, v___x_1351_, v_a_1349_);
v___x_1353_ = l_Array_append___redArg(v_b_1326_, v___x_1352_);
lean_dec_ref(v___x_1352_);
v_as_x27_1325_ = v_tail_1336_;
v_b_1326_ = v___x_1353_;
goto _start;
}
else
{
lean_dec_ref(v_b_1326_);
lean_dec_ref(v_indVal_1324_);
return v___x_1348_;
}
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_dec_ref(v_b_1326_);
lean_dec_ref(v_indVal_1324_);
v_a_1355_ = lean_ctor_get(v___x_1337_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1337_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1337_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___boxed(lean_object* v_indVal_1363_, lean_object* v_as_x27_1364_, lean_object* v_b_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg(v_indVal_1363_, v_as_x27_1364_, v_b_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
lean_dec(v_as_x27_1364_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts(lean_object* v_indVal_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_){
_start:
{
lean_object* v_ctors_1382_; lean_object* v_alts_1383_; lean_object* v___x_1384_; 
v_ctors_1382_ = lean_ctor_get(v_indVal_1374_, 4);
lean_inc(v_ctors_1382_);
v_alts_1383_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__2));
v___x_1384_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg(v_indVal_1374_, v_ctors_1382_, v_alts_1383_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_);
lean_dec(v_ctors_1382_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1394_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1387_ = v___x_1384_;
v_isShared_1388_ = v_isSharedCheck_1394_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1384_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1394_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1392_; 
v___x_1389_ = lean_array_pop(v_a_1385_);
v___x_1390_ = lean_array_pop(v___x_1389_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 0, v___x_1390_);
v___x_1392_ = v___x_1387_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1390_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
else
{
return v___x_1384_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts___boxed(lean_object* v_indVal_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts(v_indVal_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_, v_a_1401_);
lean_dec(v_a_1401_);
lean_dec_ref(v_a_1400_);
lean_dec(v_a_1399_);
lean_dec_ref(v_a_1398_);
lean_dec(v_a_1397_);
lean_dec_ref(v_a_1396_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2(lean_object* v_upperBound_1404_, lean_object* v___x_1405_, lean_object* v_xs_1406_, lean_object* v_a_1407_, lean_object* v_inst_1408_, lean_object* v_R_1409_, lean_object* v_a_1410_, lean_object* v_b_1411_, lean_object* v_c_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg(v_upperBound_1404_, v___x_1405_, v_xs_1406_, v_a_1407_, v_a_1410_, v_b_1411_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___boxed(lean_object* v_upperBound_1421_, lean_object* v___x_1422_, lean_object* v_xs_1423_, lean_object* v_a_1424_, lean_object* v_inst_1425_, lean_object* v_R_1426_, lean_object* v_a_1427_, lean_object* v_b_1428_, lean_object* v_c_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2(v_upperBound_1421_, v___x_1422_, v_xs_1423_, v_a_1424_, v_inst_1425_, v_R_1426_, v_a_1427_, v_b_1428_, v_c_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec_ref(v_a_1424_);
lean_dec_ref(v_xs_1423_);
lean_dec(v___x_1422_);
lean_dec(v_upperBound_1421_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3(lean_object* v_upperBound_1438_, lean_object* v_inst_1439_, lean_object* v_R_1440_, lean_object* v_a_1441_, lean_object* v_b_1442_, lean_object* v_c_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3___redArg(v_upperBound_1438_, v_a_1441_, v_b_1442_, v___y_1448_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3___boxed(lean_object* v_upperBound_1452_, lean_object* v_inst_1453_, lean_object* v_R_1454_, lean_object* v_a_1455_, lean_object* v_b_1456_, lean_object* v_c_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__3(v_upperBound_1452_, v_inst_1453_, v_R_1454_, v_a_1455_, v_b_1456_, v_c_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v_upperBound_1452_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4(lean_object* v_upperBound_1466_, lean_object* v_inst_1467_, lean_object* v_R_1468_, lean_object* v_a_1469_, lean_object* v_b_1470_, lean_object* v_c_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4___redArg(v_upperBound_1466_, v_a_1469_, v_b_1470_, v___y_1476_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4___boxed(lean_object* v_upperBound_1480_, lean_object* v_inst_1481_, lean_object* v_R_1482_, lean_object* v_a_1483_, lean_object* v_b_1484_, lean_object* v_c_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__4(v_upperBound_1480_, v_inst_1481_, v_R_1482_, v_a_1483_, v_b_1484_, v_c_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v_upperBound_1480_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7(lean_object* v_indVal_1494_, lean_object* v_as_1495_, lean_object* v_as_x27_1496_, lean_object* v_b_1497_, lean_object* v_a_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg(v_indVal_1494_, v_as_x27_1496_, v_b_1497_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___boxed(lean_object* v_indVal_1507_, lean_object* v_as_1508_, lean_object* v_as_x27_1509_, lean_object* v_b_1510_, lean_object* v_a_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7(v_indVal_1507_, v_as_1508_, v_as_x27_1509_, v_b_1510_, v_a_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v_as_x27_1509_);
lean_dec(v_as_1508_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0(lean_object* v_00_u03b1_1520_, lean_object* v_msg_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0___redArg(v_msg_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1530_, lean_object* v_msg_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0(v_00_u03b1_1530_, v_msg_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3(lean_object* v_msgData_1540_, lean_object* v_macroStack_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg(v_msgData_1540_, v_macroStack_1541_, v___y_1546_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___boxed(lean_object* v_msgData_1550_, lean_object* v_macroStack_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3(v_msgData_1550_, v_macroStack_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld(lean_object* v_header_1573_, lean_object* v_indVal_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_){
_start:
{
lean_object* v___x_1582_; 
lean_inc_ref(v_indVal_1574_);
v___x_1582_ = l_Lean_Elab_Deriving_mkDiscrs(v_header_1573_, v_indVal_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1584_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref_known(v___x_1582_, 1);
v___x_1584_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts(v_indVal_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1615_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1587_ = v___x_1584_;
v_isShared_1588_ = v_isSharedCheck_1615_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1615_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v_ref_1589_; uint8_t v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; size_t v_sz_1598_; size_t v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1613_; 
v_ref_1589_ = lean_ctor_get(v_a_1579_, 4);
v___x_1590_ = 0;
v___x_1591_ = l_Lean_SourceInfo_fromRef(v_ref_1589_, v___x_1590_);
v___x_1592_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__0));
v___x_1593_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__1));
lean_inc_n(v___x_1591_, 6);
v___x_1594_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1591_);
lean_ctor_set(v___x_1594_, 1, v___x_1592_);
v___x_1595_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_1596_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11);
v___x_1597_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1591_);
lean_ctor_set(v___x_1597_, 1, v___x_1595_);
lean_ctor_set(v___x_1597_, 2, v___x_1596_);
v_sz_1598_ = lean_array_size(v_a_1583_);
v___x_1599_ = ((size_t)0ULL);
v___x_1600_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__1(v_sz_1598_, v___x_1599_, v_a_1583_);
v___x_1601_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__14, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__14_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__14);
v___x_1602_ = l_Lean_mkSepArray(v___x_1600_, v___x_1601_);
lean_dec_ref(v___x_1600_);
v___x_1603_ = l_Array_append___redArg(v___x_1596_, v___x_1602_);
lean_dec_ref(v___x_1602_);
v___x_1604_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1591_);
lean_ctor_set(v___x_1604_, 1, v___x_1595_);
lean_ctor_set(v___x_1604_, 2, v___x_1603_);
v___x_1605_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__2));
v___x_1606_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1591_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
v___x_1607_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__4));
v___x_1608_ = l_Array_append___redArg(v___x_1596_, v_a_1585_);
lean_dec(v_a_1585_);
v___x_1609_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1591_);
lean_ctor_set(v___x_1609_, 1, v___x_1595_);
lean_ctor_set(v___x_1609_, 2, v___x_1608_);
v___x_1610_ = l_Lean_Syntax_node1(v___x_1591_, v___x_1607_, v___x_1609_);
lean_inc_ref(v___x_1597_);
v___x_1611_ = l_Lean_Syntax_node6(v___x_1591_, v___x_1593_, v___x_1594_, v___x_1597_, v___x_1597_, v___x_1604_, v___x_1606_, v___x_1610_);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v___x_1611_);
v___x_1613_ = v___x_1587_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1611_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
lean_dec(v_a_1583_);
v_a_1616_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1584_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1584_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
lean_dec_ref(v_indVal_1574_);
v_a_1624_ = lean_ctor_get(v___x_1582_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1582_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1582_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1582_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___boxed(lean_object* v_header_1632_, lean_object* v_indVal_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld(v_header_1632_, v_indVal_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_);
lean_dec(v_a_1639_);
lean_dec_ref(v_a_1638_);
lean_dec(v_a_1637_);
lean_dec_ref(v_a_1636_);
lean_dec(v_a_1635_);
lean_dec_ref(v_a_1634_);
return v_res_1641_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1(lean_object* v_msg_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_24818__overap_1652_; lean_object* v___x_1653_; 
v___x_1651_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___closed__0, &l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___closed__0);
v___x_24818__overap_1652_ = lean_panic_fn_borrowed(v___x_1651_, v_msg_1643_);
lean_inc(v___y_1649_);
lean_inc_ref(v___y_1648_);
lean_inc(v___y_1647_);
lean_inc_ref(v___y_1646_);
lean_inc(v___y_1645_);
lean_inc_ref(v___y_1644_);
v___x_1653_ = lean_apply_7(v___x_24818__overap_1652_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_, lean_box(0));
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1___boxed(lean_object* v_msg_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1(v_msg_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
lean_dec(v___y_1660_);
lean_dec_ref(v___y_1659_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg___lam__0(uint8_t v_a_1663_, lean_object* v___x_1664_, lean_object* v___x_1665_, lean_object* v_snd_1666_, lean_object* v_rhs_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v_toCold_1675_; lean_object* v_ref_1676_; lean_object* v_currMacroScope_1677_; lean_object* v_quotContext_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v_toCold_1675_ = lean_ctor_get(v___y_1672_, 0);
v_ref_1676_ = lean_ctor_get(v___y_1672_, 4);
v_currMacroScope_1677_ = lean_ctor_get(v___y_1672_, 9);
v_quotContext_1678_ = lean_ctor_get(v_toCold_1675_, 2);
v___x_1679_ = l_Lean_SourceInfo_fromRef(v_ref_1676_, v_a_1663_);
v___x_1680_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3));
v___x_1681_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__5);
v___x_1682_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__8));
lean_inc_n(v_currMacroScope_1677_, 3);
lean_inc_n(v_quotContext_1678_, 3);
v___x_1683_ = l_Lean_addMacroScope(v_quotContext_1678_, v___x_1682_, v_currMacroScope_1677_);
v___x_1684_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__12));
lean_inc_n(v___x_1679_, 11);
v___x_1685_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1679_);
lean_ctor_set(v___x_1685_, 1, v___x_1681_);
lean_ctor_set(v___x_1685_, 2, v___x_1683_);
lean_ctor_set(v___x_1685_, 3, v___x_1684_);
v___x_1686_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_1687_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__16));
v___x_1688_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18));
v___x_1689_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__19));
v___x_1690_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1679_);
lean_ctor_set(v___x_1690_, 1, v___x_1689_);
v___x_1691_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__21));
v___x_1692_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23);
v___x_1693_ = lean_box(0);
v___x_1694_ = l_Lean_addMacroScope(v_quotContext_1678_, v___x_1693_, v_currMacroScope_1677_);
v___x_1695_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__33));
v___x_1696_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1679_);
lean_ctor_set(v___x_1696_, 1, v___x_1692_);
lean_ctor_set(v___x_1696_, 2, v___x_1694_);
lean_ctor_set(v___x_1696_, 3, v___x_1695_);
v___x_1697_ = l_Lean_Syntax_node1(v___x_1679_, v___x_1691_, v___x_1696_);
v___x_1698_ = l_Lean_Syntax_node2(v___x_1679_, v___x_1688_, v___x_1690_, v___x_1697_);
v___x_1699_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35);
v___x_1700_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__36));
v___x_1701_ = l_Lean_addMacroScope(v_quotContext_1678_, v___x_1700_, v_currMacroScope_1677_);
v___x_1702_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__39));
v___x_1703_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1679_);
lean_ctor_set(v___x_1703_, 1, v___x_1699_);
lean_ctor_set(v___x_1703_, 2, v___x_1701_);
lean_ctor_set(v___x_1703_, 3, v___x_1702_);
v___x_1704_ = l_Lean_Syntax_node2(v___x_1679_, v___x_1686_, v___x_1664_, v___x_1665_);
v___x_1705_ = l_Lean_Syntax_node2(v___x_1679_, v___x_1680_, v___x_1703_, v___x_1704_);
v___x_1706_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__40));
v___x_1707_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1679_);
lean_ctor_set(v___x_1707_, 1, v___x_1706_);
v___x_1708_ = l_Lean_Syntax_node3(v___x_1679_, v___x_1687_, v___x_1698_, v___x_1705_, v___x_1707_);
v___x_1709_ = l_Lean_Syntax_node2(v___x_1679_, v___x_1686_, v___x_1708_, v_rhs_1667_);
v___x_1710_ = l_Lean_Syntax_node2(v___x_1679_, v___x_1680_, v___x_1685_, v___x_1709_);
lean_inc(v___y_1673_);
lean_inc_ref(v___y_1672_);
lean_inc(v___y_1671_);
lean_inc_ref(v___y_1670_);
lean_inc(v___y_1669_);
lean_inc_ref(v___y_1668_);
v___x_1711_ = lean_apply_8(v_snd_1666_, v___x_1710_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, lean_box(0));
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg___lam__0___boxed(lean_object* v_a_1712_, lean_object* v___x_1713_, lean_object* v___x_1714_, lean_object* v_snd_1715_, lean_object* v_rhs_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
uint8_t v_a_26092__boxed_1724_; lean_object* v_res_1725_; 
v_a_26092__boxed_1724_ = lean_unbox(v_a_1712_);
v_res_1725_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg___lam__0(v_a_26092__boxed_1724_, v___x_1713_, v___x_1714_, v_snd_1715_, v_rhs_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg(lean_object* v_upperBound_1727_, lean_object* v_indVal_1728_, lean_object* v_xs_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_b_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v_a_1739_; uint8_t v___x_1743_; 
v___x_1743_ = lean_nat_dec_lt(v_a_1731_, v_upperBound_1727_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; 
lean_dec(v_a_1731_);
v___x_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1744_, 0, v_b_1732_);
return v___x_1744_;
}
else
{
lean_object* v_snd_1745_; lean_object* v_fst_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1847_; 
v_snd_1745_ = lean_ctor_get(v_b_1732_, 1);
v_fst_1746_ = lean_ctor_get(v_b_1732_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v_b_1732_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1748_ = v_b_1732_;
v_isShared_1749_ = v_isSharedCheck_1847_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_snd_1745_);
lean_inc(v_fst_1746_);
lean_dec(v_b_1732_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1847_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v_fst_1750_; lean_object* v_snd_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1846_; 
v_fst_1750_ = lean_ctor_get(v_snd_1745_, 0);
v_snd_1751_ = lean_ctor_get(v_snd_1745_, 1);
v_isSharedCheck_1846_ = !lean_is_exclusive(v_snd_1745_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1753_ = v_snd_1745_;
v_isShared_1754_ = v_isSharedCheck_1846_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_snd_1751_);
lean_inc(v_fst_1750_);
lean_dec(v_snd_1745_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1846_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v_numParams_1755_; lean_object* v_lctx_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; 
v_numParams_1755_ = lean_ctor_get(v_indVal_1728_, 1);
v_lctx_1756_ = lean_ctor_get(v___y_1733_, 2);
v___x_1757_ = l_Lean_instInhabitedExpr;
v___x_1758_ = lean_nat_add(v_numParams_1755_, v_a_1731_);
v___x_1759_ = lean_array_get_borrowed(v___x_1757_, v_xs_1729_, v___x_1758_);
lean_dec(v___x_1758_);
lean_inc(v___x_1759_);
lean_inc_ref(v_lctx_1756_);
v___x_1760_ = l_Lean_Meta_occursOrInType(v_lctx_1756_, v___x_1759_, v_a_1730_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = l_Lean_Expr_fvarId_x21(v___x_1759_);
v___x_1762_ = l_Lean_FVarId_getUserName___redArg(v___x_1761_, v___y_1733_, v___y_1735_, v___y_1736_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v_a_1763_; lean_object* v___x_1764_; 
v_a_1763_ = lean_ctor_get(v___x_1762_, 0);
lean_inc_n(v_a_1763_, 2);
lean_dec_ref_known(v___x_1762_, 1);
v___x_1764_ = l_Lean_Core_mkFreshUserName(v_a_1763_, v___y_1735_, v___y_1736_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref_known(v___x_1764_, 1);
v___x_1766_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg___closed__0));
v___x_1767_ = lean_name_append_after(v_a_1763_, v___x_1766_);
v___x_1768_ = l_Lean_Core_mkFreshUserName(v___x_1767_, v___y_1735_, v___y_1736_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1770_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1769_);
lean_dec_ref_known(v___x_1768_, 1);
lean_inc(v___y_1736_);
lean_inc_ref(v___y_1735_);
lean_inc(v___y_1734_);
lean_inc_ref(v___y_1733_);
lean_inc(v___x_1759_);
v___x_1770_ = lean_infer_type(v___x_1759_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1772_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref_known(v___x_1770_, 1);
v___x_1772_ = l_Lean_Meta_isProp(v_a_1771_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; uint8_t v___x_1778_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1773_);
lean_dec_ref_known(v___x_1772_, 1);
v___x_1774_ = l_Lean_mkIdent(v_a_1765_);
v___x_1775_ = l_Lean_mkIdent(v_a_1769_);
lean_inc(v___x_1774_);
v___x_1776_ = lean_array_push(v_fst_1746_, v___x_1774_);
lean_inc(v___x_1775_);
v___x_1777_ = lean_array_push(v_fst_1750_, v___x_1775_);
v___x_1778_ = lean_unbox(v_a_1773_);
if (v___x_1778_ == 0)
{
lean_object* v___f_1779_; lean_object* v___x_1781_; 
v___f_1779_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg___lam__0___boxed), 12, 4);
lean_closure_set(v___f_1779_, 0, v_a_1773_);
lean_closure_set(v___f_1779_, 1, v___x_1774_);
lean_closure_set(v___f_1779_, 2, v___x_1775_);
lean_closure_set(v___f_1779_, 3, v_snd_1751_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 1, v___f_1779_);
lean_ctor_set(v___x_1753_, 0, v___x_1777_);
v___x_1781_ = v___x_1753_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1777_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v___f_1779_);
v___x_1781_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1783_; 
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 1, v___x_1781_);
lean_ctor_set(v___x_1748_, 0, v___x_1776_);
v___x_1783_ = v___x_1748_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1776_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v___x_1781_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
v_a_1739_ = v___x_1783_;
goto v___jp_1738_;
}
}
}
else
{
lean_object* v___x_1787_; 
lean_dec(v___x_1775_);
lean_dec(v___x_1774_);
lean_dec(v_a_1773_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 0, v___x_1777_);
v___x_1787_ = v___x_1753_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v___x_1777_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_snd_1751_);
v___x_1787_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
lean_object* v___x_1789_; 
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 1, v___x_1787_);
lean_ctor_set(v___x_1748_, 0, v___x_1776_);
v___x_1789_ = v___x_1748_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1776_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v___x_1787_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
v_a_1739_ = v___x_1789_;
goto v___jp_1738_;
}
}
}
}
else
{
lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
lean_dec(v_a_1769_);
lean_dec(v_a_1765_);
lean_del_object(v___x_1753_);
lean_dec(v_snd_1751_);
lean_dec(v_fst_1750_);
lean_del_object(v___x_1748_);
lean_dec(v_fst_1746_);
lean_dec(v_a_1731_);
v_a_1792_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___x_1772_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_dec(v___x_1772_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_a_1792_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
else
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1807_; 
lean_dec(v_a_1769_);
lean_dec(v_a_1765_);
lean_del_object(v___x_1753_);
lean_dec(v_snd_1751_);
lean_dec(v_fst_1750_);
lean_del_object(v___x_1748_);
lean_dec(v_fst_1746_);
lean_dec(v_a_1731_);
v_a_1800_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1807_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1802_ = v___x_1770_;
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1770_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1807_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1805_; 
if (v_isShared_1803_ == 0)
{
v___x_1805_ = v___x_1802_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1800_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
else
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
lean_dec(v_a_1765_);
lean_del_object(v___x_1753_);
lean_dec(v_snd_1751_);
lean_dec(v_fst_1750_);
lean_del_object(v___x_1748_);
lean_dec(v_fst_1746_);
lean_dec(v_a_1731_);
v_a_1808_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v___x_1768_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1768_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
else
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1823_; 
lean_dec(v_a_1763_);
lean_del_object(v___x_1753_);
lean_dec(v_snd_1751_);
lean_dec(v_fst_1750_);
lean_del_object(v___x_1748_);
lean_dec(v_fst_1746_);
lean_dec(v_a_1731_);
v_a_1816_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1818_ = v___x_1764_;
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1764_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1823_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1821_; 
if (v_isShared_1819_ == 0)
{
v___x_1821_ = v___x_1818_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_a_1816_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
lean_del_object(v___x_1753_);
lean_dec(v_snd_1751_);
lean_dec(v_fst_1750_);
lean_del_object(v___x_1748_);
lean_dec(v_fst_1746_);
lean_dec(v_a_1731_);
v_a_1824_ = lean_ctor_get(v___x_1762_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1762_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1762_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1762_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
else
{
lean_object* v_ref_1832_; uint8_t v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1841_; 
v_ref_1832_ = lean_ctor_get(v___y_1735_, 4);
v___x_1833_ = 0;
v___x_1834_ = l_Lean_SourceInfo_fromRef(v_ref_1832_, v___x_1833_);
v___x_1835_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__8));
v___x_1836_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___closed__9));
lean_inc(v___x_1834_);
v___x_1837_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1834_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
v___x_1838_ = l_Lean_Syntax_node1(v___x_1834_, v___x_1835_, v___x_1837_);
v___x_1839_ = lean_array_push(v_fst_1746_, v___x_1838_);
if (v_isShared_1754_ == 0)
{
v___x_1841_ = v___x_1753_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_fst_1750_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v_snd_1751_);
v___x_1841_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
lean_object* v___x_1843_; 
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 1, v___x_1841_);
lean_ctor_set(v___x_1748_, 0, v___x_1839_);
v___x_1843_ = v___x_1748_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1839_);
lean_ctor_set(v_reuseFailAlloc_1844_, 1, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
v_a_1739_ = v___x_1843_;
goto v___jp_1738_;
}
}
}
}
}
}
v___jp_1738_:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1740_ = lean_unsigned_to_nat(1u);
v___x_1741_ = lean_nat_add(v_a_1731_, v___x_1740_);
lean_dec(v_a_1731_);
v_a_1731_ = v___x_1741_;
v_b_1732_ = v_a_1739_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg___boxed(lean_object* v_upperBound_1848_, lean_object* v_indVal_1849_, lean_object* v_xs_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_b_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg(v_upperBound_1848_, v_indVal_1849_, v_xs_1850_, v_a_1851_, v_a_1852_, v_b_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec_ref(v_a_1851_);
lean_dec_ref(v_xs_1850_);
lean_dec_ref(v_indVal_1849_);
lean_dec(v_upperBound_1848_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2(lean_object* v___f_1878_, lean_object* v_numFields_1879_, lean_object* v_indVal_1880_, lean_object* v___f_1881_, lean_object* v_xs_1882_, lean_object* v_type_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = l_Lean_Core_betaReduce(v_type_1883_, v___y_1888_, v___y_1889_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_a_1892_);
lean_dec_ref_known(v___x_1891_, 1);
v___x_1893_ = lean_unsigned_to_nat(0u);
v___x_1894_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__2));
v___x_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
lean_ctor_set(v___x_1895_, 1, v___f_1878_);
v___x_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1894_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
v___x_1897_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg(v_numFields_1879_, v_indVal_1880_, v_xs_1882_, v_a_1892_, v___x_1893_, v___x_1896_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
lean_dec(v_a_1892_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; lean_object* v_snd_1899_; lean_object* v_toCold_1900_; lean_object* v_fst_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_2001_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1898_);
lean_dec_ref_known(v___x_1897_, 1);
v_snd_1899_ = lean_ctor_get(v_a_1898_, 1);
lean_inc(v_snd_1899_);
v_toCold_1900_ = lean_ctor_get(v___y_1888_, 0);
v_fst_1901_ = lean_ctor_get(v_a_1898_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v_a_1898_);
if (v_isSharedCheck_2001_ == 0)
{
lean_object* v_unused_2002_; 
v_unused_2002_ = lean_ctor_get(v_a_1898_, 1);
lean_dec(v_unused_2002_);
v___x_1903_ = v_a_1898_;
v_isShared_1904_ = v_isSharedCheck_2001_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_fst_1901_);
lean_dec(v_a_1898_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_2001_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v_fst_1905_; lean_object* v_snd_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_2000_; 
v_fst_1905_ = lean_ctor_get(v_snd_1899_, 0);
v_snd_1906_ = lean_ctor_get(v_snd_1899_, 1);
v_isSharedCheck_2000_ = !lean_is_exclusive(v_snd_1899_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1908_ = v_snd_1899_;
v_isShared_1909_ = v_isSharedCheck_2000_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_snd_1906_);
lean_inc(v_fst_1905_);
lean_dec(v_snd_1899_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_2000_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v_ref_1910_; lean_object* v_currMacroScope_1911_; lean_object* v_quotContext_1912_; uint8_t v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v_ref_1910_ = lean_ctor_get(v___y_1888_, 4);
v_currMacroScope_1911_ = lean_ctor_get(v___y_1888_, 9);
v_quotContext_1912_ = lean_ctor_get(v_toCold_1900_, 2);
v___x_1913_ = 0;
v___x_1914_ = l_Lean_SourceInfo_fromRef(v_ref_1910_, v___x_1913_);
v___x_1915_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1);
v___x_1916_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3));
lean_inc(v_currMacroScope_1911_);
lean_inc(v_quotContext_1912_);
v___x_1917_ = l_Lean_addMacroScope(v_quotContext_1912_, v___x_1916_, v_currMacroScope_1911_);
v___x_1918_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__7));
v___x_1919_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1914_);
lean_ctor_set(v___x_1919_, 1, v___x_1915_);
lean_ctor_set(v___x_1919_, 2, v___x_1917_);
lean_ctor_set(v___x_1919_, 3, v___x_1918_);
lean_inc(v___y_1889_);
lean_inc_ref(v___y_1888_);
lean_inc(v___y_1887_);
lean_inc_ref(v___y_1886_);
lean_inc(v___y_1885_);
lean_inc_ref(v___y_1884_);
v___x_1920_ = lean_apply_8(v_snd_1906_, v___x_1919_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, lean_box(0));
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v_a_1921_; lean_object* v_ctorArgs1_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___x_1969_; uint8_t v___x_1970_; 
v_a_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_a_1921_);
lean_dec_ref_known(v___x_1920_, 1);
v___x_1969_ = lean_array_get_size(v_fst_1901_);
v___x_1970_ = lean_nat_dec_eq(v___x_1969_, v___x_1893_);
if (v___x_1970_ == 0)
{
v_ctorArgs1_1923_ = v_fst_1901_;
v___y_1924_ = v___y_1884_;
v___y_1925_ = v___y_1885_;
v___y_1926_ = v___y_1886_;
v___y_1927_ = v___y_1887_;
v___y_1928_ = v___y_1888_;
v___y_1929_ = v___y_1889_;
goto v___jp_1922_;
}
else
{
lean_object* v___x_1971_; 
lean_inc_ref(v___f_1881_);
lean_inc(v___y_1889_);
lean_inc_ref(v___y_1888_);
lean_inc(v___y_1887_);
lean_inc_ref(v___y_1886_);
lean_inc(v___y_1885_);
lean_inc_ref(v___y_1884_);
v___x_1971_ = lean_apply_7(v___f_1881_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, lean_box(0));
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v_a_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
lean_inc_n(v_a_1972_, 7);
lean_dec_ref_known(v___x_1971_, 1);
v___x_1973_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__5));
v___x_1974_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18));
v___x_1975_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__19));
v___x_1976_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1976_, 0, v_a_1972_);
lean_ctor_set(v___x_1976_, 1, v___x_1975_);
v___x_1977_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__21));
v___x_1978_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23);
v___x_1979_ = lean_box(0);
lean_inc(v_currMacroScope_1911_);
lean_inc(v_quotContext_1912_);
v___x_1980_ = l_Lean_addMacroScope(v_quotContext_1912_, v___x_1979_, v_currMacroScope_1911_);
v___x_1981_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__33));
v___x_1982_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1982_, 0, v_a_1972_);
lean_ctor_set(v___x_1982_, 1, v___x_1978_);
lean_ctor_set(v___x_1982_, 2, v___x_1980_);
lean_ctor_set(v___x_1982_, 3, v___x_1981_);
v___x_1983_ = l_Lean_Syntax_node1(v_a_1972_, v___x_1977_, v___x_1982_);
v___x_1984_ = l_Lean_Syntax_node2(v_a_1972_, v___x_1974_, v___x_1976_, v___x_1983_);
v___x_1985_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_1986_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11);
v___x_1987_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1987_, 0, v_a_1972_);
lean_ctor_set(v___x_1987_, 1, v___x_1985_);
lean_ctor_set(v___x_1987_, 2, v___x_1986_);
v___x_1988_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__40));
v___x_1989_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1989_, 0, v_a_1972_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
v___x_1990_ = l_Lean_Syntax_node3(v_a_1972_, v___x_1973_, v___x_1984_, v___x_1987_, v___x_1989_);
v___x_1991_ = lean_array_push(v_fst_1901_, v___x_1990_);
v_ctorArgs1_1923_ = v___x_1991_;
v___y_1924_ = v___y_1884_;
v___y_1925_ = v___y_1885_;
v___y_1926_ = v___y_1886_;
v___y_1927_ = v___y_1887_;
v___y_1928_ = v___y_1888_;
v___y_1929_ = v___y_1889_;
goto v___jp_1922_;
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
lean_dec(v_a_1921_);
lean_del_object(v___x_1908_);
lean_dec(v_fst_1905_);
lean_del_object(v___x_1903_);
lean_dec(v_fst_1901_);
lean_dec_ref(v___f_1881_);
v_a_1992_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1971_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1971_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
v___jp_1922_:
{
lean_object* v___x_1930_; 
lean_inc(v___y_1929_);
lean_inc_ref(v___y_1928_);
lean_inc(v___y_1927_);
lean_inc_ref(v___y_1926_);
lean_inc(v___y_1925_);
lean_inc_ref(v___y_1924_);
v___x_1930_ = lean_apply_7(v___f_1881_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, lean_box(0));
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1960_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1933_ = v___x_1930_;
v_isShared_1934_ = v_isSharedCheck_1960_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1930_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1960_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1938_; 
v___x_1935_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__10));
v___x_1936_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__8));
lean_inc(v_a_1931_);
if (v_isShared_1909_ == 0)
{
lean_ctor_set_tag(v___x_1908_, 2);
lean_ctor_set(v___x_1908_, 1, v___x_1936_);
lean_ctor_set(v___x_1908_, 0, v_a_1931_);
v___x_1938_ = v___x_1908_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1931_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v___x_1936_);
v___x_1938_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1942_; 
v___x_1939_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__0));
v___x_1940_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__1));
lean_inc(v_a_1931_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set_tag(v___x_1903_, 2);
lean_ctor_set(v___x_1903_, 1, v___x_1939_);
lean_ctor_set(v___x_1903_, 0, v_a_1931_);
v___x_1942_ = v___x_1903_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1931_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v___x_1939_);
v___x_1942_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1956_; 
v___x_1943_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___closed__3));
v___x_1944_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_1945_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11);
v___x_1946_ = l_Array_append___redArg(v___x_1945_, v_ctorArgs1_1923_);
lean_dec_ref(v_ctorArgs1_1923_);
v___x_1947_ = l_Array_append___redArg(v___x_1946_, v_fst_1905_);
lean_dec(v_fst_1905_);
lean_inc_n(v_a_1931_, 5);
v___x_1948_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1948_, 0, v_a_1931_);
lean_ctor_set(v___x_1948_, 1, v___x_1944_);
lean_ctor_set(v___x_1948_, 2, v___x_1947_);
v___x_1949_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1949_, 0, v_a_1931_);
lean_ctor_set(v___x_1949_, 1, v___x_1944_);
lean_ctor_set(v___x_1949_, 2, v___x_1945_);
v___x_1950_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__17));
v___x_1951_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1951_, 0, v_a_1931_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = l_Lean_Syntax_node4(v_a_1931_, v___x_1943_, v___x_1948_, v___x_1949_, v___x_1951_, v_a_1921_);
v___x_1953_ = l_Lean_Syntax_node2(v_a_1931_, v___x_1940_, v___x_1942_, v___x_1952_);
v___x_1954_ = l_Lean_Syntax_node2(v_a_1931_, v___x_1935_, v___x_1938_, v___x_1953_);
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 0, v___x_1954_);
v___x_1956_ = v___x_1933_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1954_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
}
else
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1968_; 
lean_dec_ref(v_ctorArgs1_1923_);
lean_dec(v_a_1921_);
lean_del_object(v___x_1908_);
lean_dec(v_fst_1905_);
lean_del_object(v___x_1903_);
v_a_1961_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1963_ = v___x_1930_;
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1930_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1968_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
lean_object* v___x_1966_; 
if (v_isShared_1964_ == 0)
{
v___x_1966_ = v___x_1963_;
goto v_reusejp_1965_;
}
else
{
lean_object* v_reuseFailAlloc_1967_; 
v_reuseFailAlloc_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1967_, 0, v_a_1961_);
v___x_1966_ = v_reuseFailAlloc_1967_;
goto v_reusejp_1965_;
}
v_reusejp_1965_:
{
return v___x_1966_;
}
}
}
}
}
else
{
lean_del_object(v___x_1908_);
lean_dec(v_fst_1905_);
lean_del_object(v___x_1903_);
lean_dec(v_fst_1901_);
lean_dec_ref(v___f_1881_);
return v___x_1920_;
}
}
}
}
else
{
lean_object* v_a_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2010_; 
lean_dec_ref(v___f_1881_);
v_a_2003_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_2005_ = v___x_1897_;
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_a_2003_);
lean_dec(v___x_1897_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2010_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2008_; 
if (v_isShared_2006_ == 0)
{
v___x_2008_ = v___x_2005_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_2003_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
}
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
lean_dec_ref(v___f_1881_);
lean_dec_ref(v___f_1878_);
v_a_2011_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_1891_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_1891_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___boxed(lean_object* v___f_2019_, lean_object* v_numFields_2020_, lean_object* v_indVal_2021_, lean_object* v___f_2022_, lean_object* v_xs_2023_, lean_object* v_type_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2(v___f_2019_, v_numFields_2020_, v_indVal_2021_, v___f_2022_, v_xs_2023_, v_type_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec_ref(v_xs_2023_);
lean_dec_ref(v_indVal_2021_);
lean_dec(v_numFields_2020_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__0(lean_object* v___x_2033_, lean_object* v_ctors_2034_, lean_object* v___f_2035_, lean_object* v_indVal_2036_, lean_object* v___f_2037_, lean_object* v_x_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = l_List_get_x21Internal___redArg(v___x_2033_, v_ctors_2034_, v_x_2038_);
v___x_2047_ = l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0(v___x_2046_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; lean_object* v_toConstantVal_2049_; lean_object* v_numFields_2050_; lean_object* v_type_2051_; lean_object* v___f_2052_; uint8_t v___x_2053_; lean_object* v___x_2054_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2048_);
lean_dec_ref_known(v___x_2047_, 1);
v_toConstantVal_2049_ = lean_ctor_get(v_a_2048_, 0);
lean_inc_ref(v_toConstantVal_2049_);
v_numFields_2050_ = lean_ctor_get(v_a_2048_, 4);
lean_inc(v_numFields_2050_);
lean_dec(v_a_2048_);
v_type_2051_ = lean_ctor_get(v_toConstantVal_2049_, 2);
lean_inc_ref(v_type_2051_);
lean_dec_ref(v_toConstantVal_2049_);
v___f_2052_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__2___boxed), 13, 4);
lean_closure_set(v___f_2052_, 0, v___f_2035_);
lean_closure_set(v___f_2052_, 1, v_numFields_2050_);
lean_closure_set(v___f_2052_, 2, v_indVal_2036_);
lean_closure_set(v___f_2052_, 3, v___f_2037_);
v___x_2053_ = 0;
v___x_2054_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__5___redArg(v_type_2051_, v___f_2052_, v___x_2053_, v___x_2053_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_);
return v___x_2054_;
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_dec_ref(v___f_2037_);
lean_dec_ref(v_indVal_2036_);
lean_dec_ref(v___f_2035_);
v_a_2055_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_2047_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2047_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2055_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__0___boxed(lean_object* v___x_2063_, lean_object* v_ctors_2064_, lean_object* v___f_2065_, lean_object* v_indVal_2066_, lean_object* v___f_2067_, lean_object* v_x_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__0(v___x_2063_, v_ctors_2064_, v___f_2065_, v_indVal_2066_, v___f_2067_, v_x_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v_ctors_2064_);
lean_dec(v___x_2063_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2___redArg(lean_object* v_f_2077_, lean_object* v_n_2078_, lean_object* v_x_2079_, lean_object* v_i_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
uint8_t v___x_2088_; 
v___x_2088_ = lean_nat_dec_lt(v_i_2080_, v_n_2078_);
if (v___x_2088_ == 0)
{
lean_object* v___x_2089_; 
lean_dec(v_i_2080_);
lean_dec_ref(v_f_2077_);
v___x_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2089_, 0, v_x_2079_);
return v___x_2089_;
}
else
{
lean_object* v___x_2090_; 
lean_inc_ref(v_f_2077_);
lean_inc(v___y_2086_);
lean_inc_ref(v___y_2085_);
lean_inc(v___y_2084_);
lean_inc_ref(v___y_2083_);
lean_inc(v___y_2082_);
lean_inc_ref(v___y_2081_);
lean_inc(v_i_2080_);
v___x_2090_ = lean_apply_8(v_f_2077_, v_i_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, lean_box(0));
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2091_);
lean_dec_ref_known(v___x_2090_, 1);
v___x_2092_ = lean_array_push(v_x_2079_, v_a_2091_);
v___x_2093_ = lean_unsigned_to_nat(1u);
v___x_2094_ = lean_nat_add(v_i_2080_, v___x_2093_);
lean_dec(v_i_2080_);
v_x_2079_ = v___x_2092_;
v_i_2080_ = v___x_2094_;
goto _start;
}
else
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2103_; 
lean_dec(v_i_2080_);
lean_dec_ref(v_x_2079_);
lean_dec_ref(v_f_2077_);
v_a_2096_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2098_ = v___x_2090_;
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2090_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2103_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v___x_2101_; 
if (v_isShared_2099_ == 0)
{
v___x_2101_ = v___x_2098_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
return v___x_2101_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2___redArg___boxed(lean_object* v_f_2104_, lean_object* v_n_2105_, lean_object* v_x_2106_, lean_object* v_i_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2___redArg(v_f_2104_, v_n_2105_, v_x_2106_, v_i_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v_n_2105_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2___redArg(lean_object* v_n_2116_, lean_object* v_f_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2125_ = lean_mk_empty_array_with_capacity(v_n_2116_);
v___x_2126_ = lean_unsigned_to_nat(0u);
v___x_2127_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2___redArg(v_f_2117_, v_n_2116_, v___x_2125_, v___x_2126_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2___redArg___boxed(lean_object* v_n_2128_, lean_object* v_f_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2___redArg(v_n_2128_, v_f_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v_n_2128_);
return v_res_2137_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__3(void){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2141_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__2));
v___x_2142_ = lean_unsigned_to_nat(2u);
v___x_2143_ = lean_unsigned_to_nat(87u);
v___x_2144_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__1));
v___x_2145_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__0));
v___x_2146_ = l_mkPanicMessageWithDecl(v___x_2145_, v___x_2144_, v___x_2143_, v___x_2142_, v___x_2141_);
return v___x_2146_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__9(void){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__8));
v___x_2158_ = l_String_toRawSubstring_x27(v___x_2157_);
return v___x_2158_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__27(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2205_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__26));
v___x_2206_ = l_String_toRawSubstring_x27(v___x_2205_);
return v___x_2206_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__37(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__36));
v___x_2228_ = l_String_toRawSubstring_x27(v___x_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew(lean_object* v_header_2237_, lean_object* v_indVal_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_){
_start:
{
lean_object* v_targetNames_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2442_; 
v_targetNames_2246_ = lean_ctor_get(v_header_2237_, 2);
v_isSharedCheck_2442_ = !lean_is_exclusive(v_header_2237_);
if (v_isSharedCheck_2442_ == 0)
{
lean_object* v_unused_2443_; lean_object* v_unused_2444_; lean_object* v_unused_2445_; 
v_unused_2443_ = lean_ctor_get(v_header_2237_, 3);
lean_dec(v_unused_2443_);
v_unused_2444_ = lean_ctor_get(v_header_2237_, 1);
lean_dec(v_unused_2444_);
v_unused_2445_ = lean_ctor_get(v_header_2237_, 0);
lean_dec(v_unused_2445_);
v___x_2248_ = v_header_2237_;
v_isShared_2249_ = v_isSharedCheck_2442_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_targetNames_2246_);
lean_dec(v_header_2237_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2442_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; uint8_t v___x_2252_; 
v___x_2250_ = lean_array_get_size(v_targetNames_2246_);
v___x_2251_ = lean_unsigned_to_nat(2u);
v___x_2252_ = lean_nat_dec_eq(v___x_2250_, v___x_2251_);
if (v___x_2252_ == 0)
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
lean_del_object(v___x_2248_);
lean_dec_ref(v_targetNames_2246_);
lean_dec_ref(v_indVal_2238_);
v___x_2253_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__3, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__3_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__3);
v___x_2254_ = l_panic___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__1(v___x_2253_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_);
return v___x_2254_;
}
else
{
lean_object* v_toConstantVal_2255_; lean_object* v_ctors_2256_; lean_object* v_name_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2439_; 
v_toConstantVal_2255_ = lean_ctor_get(v_indVal_2238_, 0);
lean_inc_ref(v_toConstantVal_2255_);
v_ctors_2256_ = lean_ctor_get(v_indVal_2238_, 4);
v_name_2257_ = lean_ctor_get(v_toConstantVal_2255_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v_toConstantVal_2255_);
if (v_isSharedCheck_2439_ == 0)
{
lean_object* v_unused_2440_; lean_object* v_unused_2441_; 
v_unused_2440_ = lean_ctor_get(v_toConstantVal_2255_, 2);
lean_dec(v_unused_2440_);
v_unused_2441_ = lean_ctor_get(v_toConstantVal_2255_, 1);
lean_dec(v_unused_2441_);
v___x_2259_ = v_toConstantVal_2255_;
v_isShared_2260_ = v_isSharedCheck_2439_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_name_2257_);
lean_dec(v_toConstantVal_2255_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2439_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v_ctorIdxName_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
lean_inc_n(v_name_2257_, 2);
v_ctorIdxName_2261_ = l_Lean_mkCtorIdxName(v_name_2257_);
v___x_2262_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__5));
v___x_2263_ = l_Lean_Name_append(v_name_2257_, v___x_2262_);
v___x_2264_ = l_Lean_Core_mkFreshUserName(v___x_2263_, v_a_2243_, v_a_2244_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; lean_object* v___x_2266_; 
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
lean_inc_n(v_a_2265_, 2);
lean_dec_ref_known(v___x_2264_, 1);
v___x_2266_ = l_Lean_mkCasesOnSameCtor(v_a_2265_, v_name_2257_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v___f_2267_; lean_object* v___f_2268_; lean_object* v___x_2269_; lean_object* v___f_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
lean_dec_ref_known(v___x_2266_, 1);
v___f_2267_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__1));
v___f_2268_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__0));
v___x_2269_ = lean_box(0);
lean_inc_ref(v_indVal_2238_);
lean_inc(v_ctors_2256_);
v___f_2270_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___lam__0___boxed), 13, 5);
lean_closure_set(v___f_2270_, 0, v___x_2269_);
lean_closure_set(v___f_2270_, 1, v_ctors_2256_);
lean_closure_set(v___f_2270_, 2, v___f_2268_);
lean_closure_set(v___f_2270_, 3, v_indVal_2238_);
lean_closure_set(v___f_2270_, 4, v___f_2267_);
v___x_2271_ = l_Lean_InductiveVal_numCtors(v_indVal_2238_);
lean_dec_ref(v_indVal_2238_);
v___x_2272_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2___redArg(v___x_2271_, v___f_2270_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2414_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2275_ = v___x_2272_;
v_isShared_2276_ = v_isSharedCheck_2414_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2272_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2414_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v_x1_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v_x2_2282_; uint8_t v___x_2283_; 
v___x_2277_ = lean_unsigned_to_nat(0u);
v___x_2278_ = lean_array_get_borrowed(v___x_2269_, v_targetNames_2246_, v___x_2277_);
lean_inc(v___x_2278_);
v_x1_2279_ = l_Lean_mkIdent(v___x_2278_);
v___x_2280_ = lean_unsigned_to_nat(1u);
v___x_2281_ = lean_array_get(v___x_2269_, v_targetNames_2246_, v___x_2280_);
lean_dec_ref(v_targetNames_2246_);
v_x2_2282_ = l_Lean_mkIdent(v___x_2281_);
v___x_2283_ = lean_nat_dec_eq(v___x_2271_, v___x_2280_);
lean_dec(v___x_2271_);
if (v___x_2283_ == 0)
{
lean_object* v_toCold_2284_; lean_object* v_ref_2285_; lean_object* v_currMacroScope_2286_; lean_object* v_quotContext_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2295_; 
v_toCold_2284_ = lean_ctor_get(v_a_2243_, 0);
v_ref_2285_ = lean_ctor_get(v_a_2243_, 4);
v_currMacroScope_2286_ = lean_ctor_get(v_a_2243_, 9);
v_quotContext_2287_ = lean_ctor_get(v_toCold_2284_, 2);
v___x_2288_ = l_Lean_SourceInfo_fromRef(v_ref_2285_, v___x_2283_);
v___x_2289_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__0));
v___x_2290_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__1));
lean_inc_n(v___x_2288_, 2);
v___x_2291_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2288_);
lean_ctor_set(v___x_2291_, 1, v___x_2289_);
v___x_2292_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_2293_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11);
if (v_isShared_2260_ == 0)
{
lean_ctor_set_tag(v___x_2259_, 1);
lean_ctor_set(v___x_2259_, 2, v___x_2293_);
lean_ctor_set(v___x_2259_, 1, v___x_2292_);
lean_ctor_set(v___x_2259_, 0, v___x_2288_);
v___x_2295_ = v___x_2259_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v___x_2288_);
lean_ctor_set(v_reuseFailAlloc_2388_, 1, v___x_2292_);
lean_ctor_set(v_reuseFailAlloc_2388_, 2, v___x_2293_);
v___x_2295_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2302_; 
v___x_2296_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__7));
v___x_2297_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__9, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__9_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__9);
v___x_2298_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__10));
lean_inc(v_currMacroScope_2286_);
lean_inc(v_quotContext_2287_);
v___x_2299_ = l_Lean_addMacroScope(v_quotContext_2287_, v___x_2298_, v_currMacroScope_2286_);
v___x_2300_ = lean_box(0);
lean_inc(v___x_2288_);
if (v_isShared_2249_ == 0)
{
lean_ctor_set_tag(v___x_2248_, 3);
lean_ctor_set(v___x_2248_, 3, v___x_2300_);
lean_ctor_set(v___x_2248_, 2, v___x_2299_);
lean_ctor_set(v___x_2248_, 1, v___x_2297_);
lean_ctor_set(v___x_2248_, 0, v___x_2288_);
v___x_2302_ = v___x_2248_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___x_2288_);
lean_ctor_set(v_reuseFailAlloc_2387_, 1, v___x_2297_);
lean_ctor_set(v_reuseFailAlloc_2387_, 2, v___x_2299_);
lean_ctor_set(v_reuseFailAlloc_2387_, 3, v___x_2300_);
v___x_2302_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2385_; 
v___x_2303_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__11));
lean_inc_n(v___x_2288_, 41);
v___x_2304_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2288_);
lean_ctor_set(v___x_2304_, 1, v___x_2303_);
lean_inc_ref(v___x_2302_);
v___x_2305_ = l_Lean_Syntax_node2(v___x_2288_, v___x_2292_, v___x_2302_, v___x_2304_);
v___x_2306_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3));
v___x_2307_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35);
v___x_2308_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__36));
lean_inc_n(v_currMacroScope_2286_, 6);
lean_inc_n(v_quotContext_2287_, 6);
v___x_2309_ = l_Lean_addMacroScope(v_quotContext_2287_, v___x_2308_, v_currMacroScope_2286_);
v___x_2310_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__13));
v___x_2311_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2288_);
lean_ctor_set(v___x_2311_, 1, v___x_2307_);
lean_ctor_set(v___x_2311_, 2, v___x_2309_);
lean_ctor_set(v___x_2311_, 3, v___x_2310_);
v___x_2312_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__16));
v___x_2313_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__18));
v___x_2314_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__19));
v___x_2315_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2288_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
v___x_2316_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__21));
v___x_2317_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__23);
v___x_2318_ = l_Lean_addMacroScope(v_quotContext_2287_, v___x_2269_, v_currMacroScope_2286_);
v___x_2319_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__16));
v___x_2320_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2288_);
lean_ctor_set(v___x_2320_, 1, v___x_2317_);
lean_ctor_set(v___x_2320_, 2, v___x_2318_);
lean_ctor_set(v___x_2320_, 3, v___x_2319_);
v___x_2321_ = l_Lean_Syntax_node1(v___x_2288_, v___x_2316_, v___x_2320_);
v___x_2322_ = l_Lean_Syntax_node2(v___x_2288_, v___x_2313_, v___x_2315_, v___x_2321_);
v___x_2323_ = l_Lean_mkCIdent(v_ctorIdxName_2261_);
lean_inc(v_x1_2279_);
v___x_2324_ = l_Lean_Syntax_node1(v___x_2288_, v___x_2292_, v_x1_2279_);
lean_inc(v___x_2323_);
v___x_2325_ = l_Lean_Syntax_node2(v___x_2288_, v___x_2306_, v___x_2323_, v___x_2324_);
v___x_2326_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__40));
v___x_2327_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2288_);
lean_ctor_set(v___x_2327_, 1, v___x_2326_);
lean_inc_ref_n(v___x_2327_, 2);
lean_inc_n(v___x_2322_, 2);
v___x_2328_ = l_Lean_Syntax_node3(v___x_2288_, v___x_2312_, v___x_2322_, v___x_2325_, v___x_2327_);
lean_inc(v_x2_2282_);
v___x_2329_ = l_Lean_Syntax_node1(v___x_2288_, v___x_2292_, v_x2_2282_);
v___x_2330_ = l_Lean_Syntax_node2(v___x_2288_, v___x_2306_, v___x_2323_, v___x_2329_);
v___x_2331_ = l_Lean_Syntax_node3(v___x_2288_, v___x_2312_, v___x_2322_, v___x_2330_, v___x_2327_);
v___x_2332_ = l_Lean_Syntax_node2(v___x_2288_, v___x_2292_, v___x_2328_, v___x_2331_);
v___x_2333_ = l_Lean_Syntax_node2(v___x_2288_, v___x_2306_, v___x_2311_, v___x_2332_);
v___x_2334_ = l_Lean_Syntax_node2(v___x_2288_, v___x_2296_, v___x_2305_, v___x_2333_);
v___x_2335_ = l_Lean_Syntax_node1(v___x_2288_, v___x_2292_, v___x_2334_);
v___x_2336_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__2));
v___x_2337_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2288_);
lean_ctor_set(v___x_2337_, 1, v___x_2336_);
v___x_2338_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld___closed__4));
v___x_2339_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__25));
v___x_2340_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__12));
v___x_2341_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2288_);
lean_ctor_set(v___x_2341_, 1, v___x_2340_);
v___x_2342_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__20, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__20_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__20);
v___x_2343_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__16));
v___x_2344_ = l_Lean_addMacroScope(v_quotContext_2287_, v___x_2343_, v_currMacroScope_2286_);
v___x_2345_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__19));
v___x_2346_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2288_);
lean_ctor_set(v___x_2346_, 1, v___x_2342_);
lean_ctor_set(v___x_2346_, 2, v___x_2344_);
lean_ctor_set(v___x_2346_, 3, v___x_2345_);
lean_inc_ref(v___x_2346_);
v___x_2347_ = l_Lean_Syntax_node1(v___x_2288_, v___x_2292_, v___x_2346_);
v___x_2348_ = l_Lean_Syntax_node1(v___x_2288_, v___x_2292_, v___x_2347_);
v___x_2349_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__17));
v___x_2350_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2288_);
lean_ctor_set(v___x_2350_, 1, v___x_2349_);
lean_inc_ref_n(v___x_2350_, 2);
lean_inc_ref_n(v___x_2341_, 2);
v___x_2351_ = l_Lean_Syntax_node4(v___x_2288_, v___x_2339_, v___x_2341_, v___x_2348_, v___x_2350_, v___x_2346_);
v___x_2352_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__27, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__27_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__27);
v___x_2353_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__29));
v___x_2354_ = l_Lean_addMacroScope(v_quotContext_2287_, v___x_2353_, v_currMacroScope_2286_);
v___x_2355_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__22));
v___x_2356_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2288_);
lean_ctor_set(v___x_2356_, 1, v___x_2352_);
lean_ctor_set(v___x_2356_, 2, v___x_2354_);
lean_ctor_set(v___x_2356_, 3, v___x_2355_);
lean_inc_ref(v___x_2356_);
v___x_2357_ = l_Lean_Syntax_node1(v___x_2288_, v___x_2292_, v___x_2356_);
v___x_2358_ = l_Lean_Syntax_node1(v___x_2288_, v___x_2292_, v___x_2357_);
v___x_2359_ = l_Lean_Syntax_node4(v___x_2288_, v___x_2339_, v___x_2341_, v___x_2358_, v___x_2350_, v___x_2356_);
v___x_2360_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__1);
v___x_2361_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__3));
v___x_2362_ = l_Lean_addMacroScope(v_quotContext_2287_, v___x_2361_, v_currMacroScope_2286_);
v___x_2363_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__25));
v___x_2364_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2288_);
lean_ctor_set(v___x_2364_, 1, v___x_2360_);
lean_ctor_set(v___x_2364_, 2, v___x_2362_);
lean_ctor_set(v___x_2364_, 3, v___x_2363_);
v___x_2365_ = l_Lean_Syntax_node1(v___x_2288_, v___x_2292_, v___x_2364_);
v___x_2366_ = l_Lean_Syntax_node1(v___x_2288_, v___x_2292_, v___x_2365_);
v___x_2367_ = l_Lean_mkCIdent(v_a_2265_);
v___x_2368_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__27, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__27_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__27);
v___x_2369_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__31));
v___x_2370_ = l_Lean_addMacroScope(v_quotContext_2287_, v___x_2369_, v_currMacroScope_2286_);
v___x_2371_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__35));
v___x_2372_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2288_);
lean_ctor_set(v___x_2372_, 1, v___x_2368_);
lean_ctor_set(v___x_2372_, 2, v___x_2370_);
lean_ctor_set(v___x_2372_, 3, v___x_2371_);
v___x_2373_ = l_Lean_Syntax_node1(v___x_2288_, v___x_2292_, v___x_2302_);
v___x_2374_ = l_Lean_Syntax_node2(v___x_2288_, v___x_2306_, v___x_2372_, v___x_2373_);
v___x_2375_ = l_Lean_Syntax_node3(v___x_2288_, v___x_2312_, v___x_2322_, v___x_2374_, v___x_2327_);
v___x_2376_ = l_Array_mkArray3___redArg(v_x1_2279_, v_x2_2282_, v___x_2375_);
v___x_2377_ = l_Array_append___redArg(v___x_2376_, v_a_2273_);
lean_dec(v_a_2273_);
v___x_2378_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2288_);
lean_ctor_set(v___x_2378_, 1, v___x_2292_);
lean_ctor_set(v___x_2378_, 2, v___x_2377_);
v___x_2379_ = l_Lean_Syntax_node2(v___x_2288_, v___x_2306_, v___x_2367_, v___x_2378_);
v___x_2380_ = l_Lean_Syntax_node4(v___x_2288_, v___x_2339_, v___x_2341_, v___x_2366_, v___x_2350_, v___x_2379_);
v___x_2381_ = l_Lean_Syntax_node3(v___x_2288_, v___x_2292_, v___x_2351_, v___x_2359_, v___x_2380_);
v___x_2382_ = l_Lean_Syntax_node1(v___x_2288_, v___x_2338_, v___x_2381_);
lean_inc_ref(v___x_2295_);
v___x_2383_ = l_Lean_Syntax_node6(v___x_2288_, v___x_2290_, v___x_2291_, v___x_2295_, v___x_2295_, v___x_2335_, v___x_2337_, v___x_2382_);
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 0, v___x_2383_);
v___x_2385_ = v___x_2275_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2383_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
else
{
lean_object* v_toCold_2389_; lean_object* v_ref_2390_; lean_object* v_currMacroScope_2391_; lean_object* v_quotContext_2392_; uint8_t v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2403_; 
lean_dec(v_ctorIdxName_2261_);
v_toCold_2389_ = lean_ctor_get(v_a_2243_, 0);
v_ref_2390_ = lean_ctor_get(v_a_2243_, 4);
v_currMacroScope_2391_ = lean_ctor_get(v_a_2243_, 9);
v_quotContext_2392_ = lean_ctor_get(v_toCold_2389_, 2);
v___x_2393_ = 0;
v___x_2394_ = l_Lean_SourceInfo_fromRef(v_ref_2390_, v___x_2393_);
v___x_2395_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3));
v___x_2396_ = l_Lean_mkCIdent(v_a_2265_);
v___x_2397_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_2398_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__37, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__37_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__37);
v___x_2399_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__38));
lean_inc(v_currMacroScope_2391_);
lean_inc(v_quotContext_2392_);
v___x_2400_ = l_Lean_addMacroScope(v_quotContext_2392_, v___x_2399_, v_currMacroScope_2391_);
v___x_2401_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__40));
lean_inc(v___x_2394_);
if (v_isShared_2249_ == 0)
{
lean_ctor_set_tag(v___x_2248_, 3);
lean_ctor_set(v___x_2248_, 3, v___x_2401_);
lean_ctor_set(v___x_2248_, 2, v___x_2400_);
lean_ctor_set(v___x_2248_, 1, v___x_2398_);
lean_ctor_set(v___x_2248_, 0, v___x_2394_);
v___x_2403_ = v___x_2248_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v___x_2394_);
lean_ctor_set(v_reuseFailAlloc_2413_, 1, v___x_2398_);
lean_ctor_set(v_reuseFailAlloc_2413_, 2, v___x_2400_);
lean_ctor_set(v_reuseFailAlloc_2413_, 3, v___x_2401_);
v___x_2403_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2407_; 
v___x_2404_ = l_Array_mkArray3___redArg(v_x1_2279_, v_x2_2282_, v___x_2403_);
v___x_2405_ = l_Array_append___redArg(v___x_2404_, v_a_2273_);
lean_dec(v_a_2273_);
lean_inc(v___x_2394_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set_tag(v___x_2259_, 1);
lean_ctor_set(v___x_2259_, 2, v___x_2405_);
lean_ctor_set(v___x_2259_, 1, v___x_2397_);
lean_ctor_set(v___x_2259_, 0, v___x_2394_);
v___x_2407_ = v___x_2259_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2394_);
lean_ctor_set(v_reuseFailAlloc_2412_, 1, v___x_2397_);
lean_ctor_set(v_reuseFailAlloc_2412_, 2, v___x_2405_);
v___x_2407_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
lean_object* v___x_2408_; lean_object* v___x_2410_; 
v___x_2408_ = l_Lean_Syntax_node2(v___x_2394_, v___x_2395_, v___x_2396_, v___x_2407_);
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 0, v___x_2408_);
v___x_2410_ = v___x_2275_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2408_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
}
}
else
{
lean_object* v_a_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2422_; 
lean_dec(v___x_2271_);
lean_dec(v_a_2265_);
lean_dec(v_ctorIdxName_2261_);
lean_del_object(v___x_2259_);
lean_del_object(v___x_2248_);
lean_dec_ref(v_targetNames_2246_);
v_a_2415_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2417_ = v___x_2272_;
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_a_2415_);
lean_dec(v___x_2272_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2422_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2420_; 
if (v_isShared_2418_ == 0)
{
v___x_2420_ = v___x_2417_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_a_2415_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
}
}
else
{
lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2430_; 
lean_dec(v_a_2265_);
lean_dec(v_ctorIdxName_2261_);
lean_del_object(v___x_2259_);
lean_del_object(v___x_2248_);
lean_dec_ref(v_targetNames_2246_);
lean_dec_ref(v_indVal_2238_);
v_a_2423_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2425_ = v___x_2266_;
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_dec(v___x_2266_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2428_; 
if (v_isShared_2426_ == 0)
{
v___x_2428_ = v___x_2425_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_a_2423_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
}
else
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2438_; 
lean_dec(v_ctorIdxName_2261_);
lean_del_object(v___x_2259_);
lean_dec(v_name_2257_);
lean_del_object(v___x_2248_);
lean_dec_ref(v_targetNames_2246_);
lean_dec_ref(v_indVal_2238_);
v_a_2431_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2433_ = v___x_2264_;
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2264_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2438_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2436_; 
if (v_isShared_2434_ == 0)
{
v___x_2436_ = v___x_2433_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_a_2431_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___boxed(lean_object* v_header_2446_, lean_object* v_indVal_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew(v_header_2446_, v_indVal_2447_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_, v_a_2452_, v_a_2453_);
lean_dec(v_a_2453_);
lean_dec_ref(v_a_2452_);
lean_dec(v_a_2451_);
lean_dec_ref(v_a_2450_);
lean_dec(v_a_2449_);
lean_dec_ref(v_a_2448_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0(lean_object* v_upperBound_2456_, lean_object* v_indVal_2457_, lean_object* v_xs_2458_, lean_object* v_a_2459_, lean_object* v_inst_2460_, lean_object* v_R_2461_, lean_object* v_a_2462_, lean_object* v_b_2463_, lean_object* v_c_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_){
_start:
{
lean_object* v___x_2472_; 
v___x_2472_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___redArg(v_upperBound_2456_, v_indVal_2457_, v_xs_2458_, v_a_2459_, v_a_2462_, v_b_2463_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0___boxed(lean_object* v_upperBound_2473_, lean_object* v_indVal_2474_, lean_object* v_xs_2475_, lean_object* v_a_2476_, lean_object* v_inst_2477_, lean_object* v_R_2478_, lean_object* v_a_2479_, lean_object* v_b_2480_, lean_object* v_c_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__0(v_upperBound_2473_, v_indVal_2474_, v_xs_2475_, v_a_2476_, v_inst_2477_, v_R_2478_, v_a_2479_, v_b_2480_, v_c_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec_ref(v_a_2476_);
lean_dec_ref(v_xs_2475_);
lean_dec_ref(v_indVal_2474_);
lean_dec(v_upperBound_2473_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2(lean_object* v_00_u03b1_2490_, lean_object* v_n_2491_, lean_object* v_f_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v___x_2500_; 
v___x_2500_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2___redArg(v_n_2491_, v_f_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2___boxed(lean_object* v_00_u03b1_2501_, lean_object* v_n_2502_, lean_object* v_f_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
lean_object* v_res_2511_; 
v_res_2511_ = l_Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2(v_00_u03b1_2501_, v_n_2502_, v_f_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec(v_n_2502_);
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2(lean_object* v_00_u03b1_2512_, lean_object* v_f_2513_, lean_object* v_n_2514_, lean_object* v_x_2515_, lean_object* v_i_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v___x_2524_; 
v___x_2524_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2___redArg(v_f_2513_, v_n_2514_, v_x_2515_, v_i_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2___boxed(lean_object* v_00_u03b1_2525_, lean_object* v_f_2526_, lean_object* v_n_2527_, lean_object* v_x_2528_, lean_object* v_i_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___at___00Array_ofFnM___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew_spec__2_spec__2(v_00_u03b1_2525_, v_f_2526_, v_n_2527_, v_x_2528_, v_i_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
lean_dec(v___y_2535_);
lean_dec_ref(v___y_2534_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v_n_2527_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch_spec__0(lean_object* v_opts_2538_, lean_object* v_opt_2539_){
_start:
{
lean_object* v_name_2540_; lean_object* v_defValue_2541_; lean_object* v_map_2542_; lean_object* v___x_2543_; 
v_name_2540_ = lean_ctor_get(v_opt_2539_, 0);
v_defValue_2541_ = lean_ctor_get(v_opt_2539_, 1);
v_map_2542_ = lean_ctor_get(v_opts_2538_, 0);
v___x_2543_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2542_, v_name_2540_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_inc(v_defValue_2541_);
return v_defValue_2541_;
}
else
{
lean_object* v_val_2544_; 
v_val_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_val_2544_);
lean_dec_ref_known(v___x_2543_, 1);
if (lean_obj_tag(v_val_2544_) == 3)
{
lean_object* v_v_2545_; 
v_v_2545_ = lean_ctor_get(v_val_2544_, 0);
lean_inc(v_v_2545_);
lean_dec_ref_known(v_val_2544_, 1);
return v_v_2545_;
}
else
{
lean_dec(v_val_2544_);
lean_inc(v_defValue_2541_);
return v_defValue_2541_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch_spec__0___boxed(lean_object* v_opts_2546_, lean_object* v_opt_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch_spec__0(v_opts_2546_, v_opt_2547_);
lean_dec_ref(v_opt_2547_);
lean_dec_ref(v_opts_2546_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch(lean_object* v_header_2549_, lean_object* v_indVal_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_){
_start:
{
lean_object* v_options_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; uint8_t v___x_2562_; 
v_options_2558_ = lean_ctor_get(v_a_2555_, 1);
v___x_2559_ = l___private_Lean_Elab_Deriving_Ord_0__deriving_ord_linear__construction__threshold;
v___x_2560_ = l_Lean_Option_get___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch_spec__0(v_options_2558_, v___x_2559_);
v___x_2561_ = l_Lean_InductiveVal_numCtors(v_indVal_2550_);
v___x_2562_ = lean_nat_dec_le(v___x_2560_, v___x_2561_);
lean_dec(v___x_2561_);
lean_dec(v___x_2560_);
if (v___x_2562_ == 0)
{
lean_object* v___x_2563_; 
v___x_2563_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld(v_header_2549_, v_indVal_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
return v___x_2563_;
}
else
{
lean_object* v___x_2564_; 
v___x_2564_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew(v_header_2549_, v_indVal_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_);
return v___x_2564_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch___boxed(lean_object* v_header_2565_, lean_object* v_indVal_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch(v_header_2565_, v_indVal_2566_, v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
lean_dec(v_a_2572_);
lean_dec_ref(v_a_2571_);
lean_dec(v_a_2570_);
lean_dec_ref(v_a_2569_);
lean_dec(v_a_2568_);
lean_dec_ref(v_a_2567_);
return v_res_2574_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14(void){
_start:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2613_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__6));
v___x_2614_ = l_String_toRawSubstring_x27(v___x_2613_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction(lean_object* v_ctx_2648_, lean_object* v_i_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_){
_start:
{
lean_object* v_typeInfos_2657_; lean_object* v_auxFunNames_2658_; uint8_t v_usePartial_2659_; lean_object* v___x_2660_; lean_object* v_indVal_2661_; lean_object* v___x_2662_; 
v_typeInfos_2657_ = lean_ctor_get(v_ctx_2648_, 1);
v_auxFunNames_2658_ = lean_ctor_get(v_ctx_2648_, 2);
v_usePartial_2659_ = lean_ctor_get_uint8(v_ctx_2648_, sizeof(void*)*3);
v___x_2660_ = l_Lean_instInhabitedInductiveVal_default;
v_indVal_2661_ = lean_array_get_borrowed(v___x_2660_, v_typeInfos_2657_, v_i_2649_);
lean_inc(v_indVal_2661_);
v___x_2662_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader(v_indVal_2661_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2663_; lean_object* v___x_2664_; 
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
lean_inc_n(v_a_2663_, 2);
lean_dec_ref_known(v___x_2662_, 1);
lean_inc(v_indVal_2661_);
v___x_2664_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatch(v_a_2663_, v_indVal_2661_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2798_; 
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2667_ = v___x_2664_;
v_isShared_2668_ = v_isSharedCheck_2798_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2664_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2798_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2669_; lean_object* v_auxFunName_2670_; lean_object* v_body_2672_; lean_object* v___y_2673_; 
v___x_2669_ = lean_box(0);
v_auxFunName_2670_ = lean_array_get_borrowed(v___x_2669_, v_auxFunNames_2658_, v_i_2649_);
if (v_usePartial_2659_ == 0)
{
v_body_2672_ = v_a_2665_;
v___y_2673_ = v_a_2654_;
goto v___jp_2671_;
}
else
{
lean_object* v_argNames_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v_argNames_2784_ = lean_ctor_get(v_a_2663_, 1);
v___x_2785_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader___closed__0));
lean_inc_ref(v_argNames_2784_);
v___x_2786_ = l_Lean_Elab_Deriving_mkLocalInstanceLetDecls(v_ctx_2648_, v___x_2785_, v_argNames_2784_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v_a_2787_; lean_object* v___x_2788_; 
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2787_);
lean_dec_ref_known(v___x_2786_, 1);
v___x_2788_ = l_Lean_Elab_Deriving_mkLet(v_a_2787_, v_a_2665_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_);
lean_dec(v_a_2787_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2789_);
lean_dec_ref_known(v___x_2788_, 1);
v_body_2672_ = v_a_2789_;
v___y_2673_ = v_a_2654_;
goto v___jp_2671_;
}
else
{
lean_del_object(v___x_2667_);
lean_dec(v_a_2663_);
return v___x_2788_;
}
}
else
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2797_; 
lean_del_object(v___x_2667_);
lean_dec(v_a_2665_);
lean_dec(v_a_2663_);
v_a_2790_ = lean_ctor_get(v___x_2786_, 0);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2792_ = v___x_2786_;
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___x_2786_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2795_; 
if (v_isShared_2793_ == 0)
{
v___x_2795_ = v___x_2792_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_a_2790_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
}
v___jp_2671_:
{
if (v_usePartial_2659_ == 0)
{
lean_object* v_toCold_2674_; lean_object* v_binders_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2722_; 
v_toCold_2674_ = lean_ctor_get(v___y_2673_, 0);
v_binders_2675_ = lean_ctor_get(v_a_2663_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v_a_2663_);
if (v_isSharedCheck_2722_ == 0)
{
lean_object* v_unused_2723_; lean_object* v_unused_2724_; lean_object* v_unused_2725_; 
v_unused_2723_ = lean_ctor_get(v_a_2663_, 3);
lean_dec(v_unused_2723_);
v_unused_2724_ = lean_ctor_get(v_a_2663_, 2);
lean_dec(v_unused_2724_);
v_unused_2725_ = lean_ctor_get(v_a_2663_, 1);
lean_dec(v_unused_2725_);
v___x_2677_ = v_a_2663_;
v_isShared_2678_ = v_isSharedCheck_2722_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_binders_2675_);
lean_dec(v_a_2663_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2722_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v_ref_2679_; lean_object* v_currMacroScope_2680_; lean_object* v_quotContext_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2706_; 
v_ref_2679_ = lean_ctor_get(v___y_2673_, 4);
v_currMacroScope_2680_ = lean_ctor_get(v___y_2673_, 9);
v_quotContext_2681_ = lean_ctor_get(v_toCold_2674_, 2);
v___x_2682_ = l_Lean_SourceInfo_fromRef(v_ref_2679_, v_usePartial_2659_);
v___x_2683_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__2));
v___x_2684_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__4));
v___x_2685_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_2686_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11);
lean_inc_n(v___x_2682_, 7);
v___x_2687_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2682_);
lean_ctor_set(v___x_2687_, 1, v___x_2685_);
lean_ctor_set(v___x_2687_, 2, v___x_2686_);
lean_inc_ref_n(v___x_2687_, 8);
v___x_2688_ = l_Lean_Syntax_node7(v___x_2682_, v___x_2684_, v___x_2687_, v___x_2687_, v___x_2687_, v___x_2687_, v___x_2687_, v___x_2687_, v___x_2687_);
v___x_2689_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__6));
v___x_2690_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__7));
v___x_2691_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2682_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
v___x_2692_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__9));
lean_inc(v_auxFunName_2670_);
v___x_2693_ = l_Lean_mkIdent(v_auxFunName_2670_);
v___x_2694_ = l_Lean_Syntax_node2(v___x_2682_, v___x_2692_, v___x_2693_, v___x_2687_);
v___x_2695_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__11));
v___x_2696_ = l_Array_append___redArg(v___x_2686_, v_binders_2675_);
lean_dec_ref(v_binders_2675_);
v___x_2697_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2682_);
lean_ctor_set(v___x_2697_, 1, v___x_2685_);
lean_ctor_set(v___x_2697_, 2, v___x_2696_);
v___x_2698_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__13));
v___x_2699_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__11));
v___x_2700_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2682_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
v___x_2701_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14);
v___x_2702_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__15));
lean_inc(v_currMacroScope_2680_);
lean_inc(v_quotContext_2681_);
v___x_2703_ = l_Lean_addMacroScope(v_quotContext_2681_, v___x_2702_, v_currMacroScope_2680_);
v___x_2704_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__19));
if (v_isShared_2678_ == 0)
{
lean_ctor_set_tag(v___x_2677_, 3);
lean_ctor_set(v___x_2677_, 3, v___x_2704_);
lean_ctor_set(v___x_2677_, 2, v___x_2703_);
lean_ctor_set(v___x_2677_, 1, v___x_2701_);
lean_ctor_set(v___x_2677_, 0, v___x_2682_);
v___x_2706_ = v___x_2677_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v___x_2682_);
lean_ctor_set(v_reuseFailAlloc_2721_, 1, v___x_2701_);
lean_ctor_set(v_reuseFailAlloc_2721_, 2, v___x_2703_);
lean_ctor_set(v_reuseFailAlloc_2721_, 3, v___x_2704_);
v___x_2706_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2719_; 
lean_inc_n(v___x_2682_, 7);
v___x_2707_ = l_Lean_Syntax_node2(v___x_2682_, v___x_2698_, v___x_2700_, v___x_2706_);
v___x_2708_ = l_Lean_Syntax_node1(v___x_2682_, v___x_2685_, v___x_2707_);
v___x_2709_ = l_Lean_Syntax_node2(v___x_2682_, v___x_2695_, v___x_2697_, v___x_2708_);
v___x_2710_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__21));
v___x_2711_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__22));
v___x_2712_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2682_);
lean_ctor_set(v___x_2712_, 1, v___x_2711_);
v___x_2713_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__25));
lean_inc_ref_n(v___x_2687_, 3);
v___x_2714_ = l_Lean_Syntax_node2(v___x_2682_, v___x_2713_, v___x_2687_, v___x_2687_);
v___x_2715_ = l_Lean_Syntax_node4(v___x_2682_, v___x_2710_, v___x_2712_, v_body_2672_, v___x_2714_, v___x_2687_);
v___x_2716_ = l_Lean_Syntax_node5(v___x_2682_, v___x_2689_, v___x_2691_, v___x_2694_, v___x_2709_, v___x_2715_, v___x_2687_);
v___x_2717_ = l_Lean_Syntax_node2(v___x_2682_, v___x_2683_, v___x_2688_, v___x_2716_);
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 0, v___x_2717_);
v___x_2719_ = v___x_2667_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v___x_2717_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
}
else
{
lean_object* v_toCold_2726_; lean_object* v_binders_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2780_; 
v_toCold_2726_ = lean_ctor_get(v___y_2673_, 0);
v_binders_2727_ = lean_ctor_get(v_a_2663_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v_a_2663_);
if (v_isSharedCheck_2780_ == 0)
{
lean_object* v_unused_2781_; lean_object* v_unused_2782_; lean_object* v_unused_2783_; 
v_unused_2781_ = lean_ctor_get(v_a_2663_, 3);
lean_dec(v_unused_2781_);
v_unused_2782_ = lean_ctor_get(v_a_2663_, 2);
lean_dec(v_unused_2782_);
v_unused_2783_ = lean_ctor_get(v_a_2663_, 1);
lean_dec(v_unused_2783_);
v___x_2729_ = v_a_2663_;
v_isShared_2730_ = v_isSharedCheck_2780_;
goto v_resetjp_2728_;
}
else
{
lean_inc(v_binders_2727_);
lean_dec(v_a_2663_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2780_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v_ref_2731_; lean_object* v_currMacroScope_2732_; lean_object* v_quotContext_2733_; uint8_t v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2764_; 
v_ref_2731_ = lean_ctor_get(v___y_2673_, 4);
v_currMacroScope_2732_ = lean_ctor_get(v___y_2673_, 9);
v_quotContext_2733_ = lean_ctor_get(v_toCold_2726_, 2);
v___x_2734_ = 0;
v___x_2735_ = l_Lean_SourceInfo_fromRef(v_ref_2731_, v___x_2734_);
v___x_2736_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__2));
v___x_2737_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__4));
v___x_2738_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_2739_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11);
lean_inc_n(v___x_2735_, 10);
v___x_2740_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2735_);
lean_ctor_set(v___x_2740_, 1, v___x_2738_);
lean_ctor_set(v___x_2740_, 2, v___x_2739_);
v___x_2741_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__26));
v___x_2742_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__27));
v___x_2743_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2735_);
lean_ctor_set(v___x_2743_, 1, v___x_2741_);
v___x_2744_ = l_Lean_Syntax_node1(v___x_2735_, v___x_2742_, v___x_2743_);
v___x_2745_ = l_Lean_Syntax_node1(v___x_2735_, v___x_2738_, v___x_2744_);
lean_inc_ref_n(v___x_2740_, 7);
v___x_2746_ = l_Lean_Syntax_node7(v___x_2735_, v___x_2737_, v___x_2740_, v___x_2740_, v___x_2740_, v___x_2740_, v___x_2740_, v___x_2740_, v___x_2745_);
v___x_2747_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__6));
v___x_2748_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__7));
v___x_2749_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2735_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
v___x_2750_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__9));
lean_inc(v_auxFunName_2670_);
v___x_2751_ = l_Lean_mkIdent(v_auxFunName_2670_);
v___x_2752_ = l_Lean_Syntax_node2(v___x_2735_, v___x_2750_, v___x_2751_, v___x_2740_);
v___x_2753_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__11));
v___x_2754_ = l_Array_append___redArg(v___x_2739_, v_binders_2727_);
lean_dec_ref(v_binders_2727_);
v___x_2755_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2735_);
lean_ctor_set(v___x_2755_, 1, v___x_2738_);
lean_ctor_set(v___x_2755_, 2, v___x_2754_);
v___x_2756_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__13));
v___x_2757_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__11));
v___x_2758_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2735_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
v___x_2759_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14);
v___x_2760_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__15));
lean_inc(v_currMacroScope_2732_);
lean_inc(v_quotContext_2733_);
v___x_2761_ = l_Lean_addMacroScope(v_quotContext_2733_, v___x_2760_, v_currMacroScope_2732_);
v___x_2762_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__19));
if (v_isShared_2730_ == 0)
{
lean_ctor_set_tag(v___x_2729_, 3);
lean_ctor_set(v___x_2729_, 3, v___x_2762_);
lean_ctor_set(v___x_2729_, 2, v___x_2761_);
lean_ctor_set(v___x_2729_, 1, v___x_2759_);
lean_ctor_set(v___x_2729_, 0, v___x_2735_);
v___x_2764_ = v___x_2729_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2735_);
lean_ctor_set(v_reuseFailAlloc_2779_, 1, v___x_2759_);
lean_ctor_set(v_reuseFailAlloc_2779_, 2, v___x_2761_);
lean_ctor_set(v_reuseFailAlloc_2779_, 3, v___x_2762_);
v___x_2764_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2777_; 
lean_inc_n(v___x_2735_, 7);
v___x_2765_ = l_Lean_Syntax_node2(v___x_2735_, v___x_2756_, v___x_2758_, v___x_2764_);
v___x_2766_ = l_Lean_Syntax_node1(v___x_2735_, v___x_2738_, v___x_2765_);
v___x_2767_ = l_Lean_Syntax_node2(v___x_2735_, v___x_2753_, v___x_2755_, v___x_2766_);
v___x_2768_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__21));
v___x_2769_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__22));
v___x_2770_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2770_, 0, v___x_2735_);
lean_ctor_set(v___x_2770_, 1, v___x_2769_);
v___x_2771_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__25));
lean_inc_ref_n(v___x_2740_, 3);
v___x_2772_ = l_Lean_Syntax_node2(v___x_2735_, v___x_2771_, v___x_2740_, v___x_2740_);
v___x_2773_ = l_Lean_Syntax_node4(v___x_2735_, v___x_2768_, v___x_2770_, v_body_2672_, v___x_2772_, v___x_2740_);
v___x_2774_ = l_Lean_Syntax_node5(v___x_2735_, v___x_2747_, v___x_2749_, v___x_2752_, v___x_2767_, v___x_2773_, v___x_2740_);
v___x_2775_ = l_Lean_Syntax_node2(v___x_2735_, v___x_2736_, v___x_2746_, v___x_2774_);
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 0, v___x_2775_);
v___x_2777_ = v___x_2667_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2775_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2663_);
return v___x_2664_;
}
}
else
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
v_a_2799_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2801_ = v___x_2662_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2662_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2804_; 
if (v_isShared_2802_ == 0)
{
v___x_2804_ = v___x_2801_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___boxed(lean_object* v_ctx_2807_, lean_object* v_i_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction(v_ctx_2807_, v_i_2808_, v_a_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_);
lean_dec(v_a_2814_);
lean_dec_ref(v_a_2813_);
lean_dec(v_a_2812_);
lean_dec_ref(v_a_2811_);
lean_dec(v_a_2810_);
lean_dec_ref(v_a_2809_);
lean_dec(v_i_2808_);
lean_dec_ref(v_ctx_2807_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0___redArg(lean_object* v_upperBound_2817_, lean_object* v_ctx_2818_, lean_object* v_a_2819_, lean_object* v_b_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_){
_start:
{
uint8_t v___x_2828_; 
v___x_2828_ = lean_nat_dec_lt(v_a_2819_, v_upperBound_2817_);
if (v___x_2828_ == 0)
{
lean_object* v___x_2829_; 
lean_dec(v_a_2819_);
v___x_2829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2829_, 0, v_b_2820_);
return v___x_2829_;
}
else
{
lean_object* v___x_2830_; 
v___x_2830_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction(v_ctx_2818_, v_a_2819_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref_known(v___x_2830_, 1);
v___x_2832_ = lean_array_push(v_b_2820_, v_a_2831_);
v___x_2833_ = lean_unsigned_to_nat(1u);
v___x_2834_ = lean_nat_add(v_a_2819_, v___x_2833_);
lean_dec(v_a_2819_);
v_a_2819_ = v___x_2834_;
v_b_2820_ = v___x_2832_;
goto _start;
}
else
{
lean_object* v_a_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
lean_dec_ref(v_b_2820_);
lean_dec(v_a_2819_);
v_a_2836_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2838_ = v___x_2830_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_a_2836_);
lean_dec(v___x_2830_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2841_; 
if (v_isShared_2839_ == 0)
{
v___x_2841_ = v___x_2838_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_a_2836_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0___redArg___boxed(lean_object* v_upperBound_2844_, lean_object* v_ctx_2845_, lean_object* v_a_2846_, lean_object* v_b_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_){
_start:
{
lean_object* v_res_2855_; 
v_res_2855_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0___redArg(v_upperBound_2844_, v_ctx_2845_, v_a_2846_, v_b_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
lean_dec(v___y_2851_);
lean_dec_ref(v___y_2850_);
lean_dec(v___y_2849_);
lean_dec_ref(v___y_2848_);
lean_dec_ref(v_ctx_2845_);
lean_dec(v_upperBound_2844_);
return v_res_2855_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__5(void){
_start:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2869_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__4));
v___x_2870_ = l_String_toRawSubstring_x27(v___x_2869_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock(lean_object* v_ctx_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_){
_start:
{
lean_object* v_typeInfos_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v_auxDefs_2897_; lean_object* v___x_2898_; 
v_typeInfos_2894_ = lean_ctor_get(v_ctx_2886_, 1);
v___x_2895_ = lean_array_get_size(v_typeInfos_2894_);
v___x_2896_ = lean_unsigned_to_nat(0u);
v_auxDefs_2897_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___closed__2));
v___x_2898_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0___redArg(v___x_2895_, v_ctx_2886_, v___x_2896_, v_auxDefs_2897_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v_toCold_2899_; lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2935_; 
v_toCold_2899_ = lean_ctor_get(v_a_2891_, 0);
v_a_2900_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2902_ = v___x_2898_;
v_isShared_2903_ = v_isSharedCheck_2935_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2898_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2935_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v_ref_2904_; lean_object* v_currMacroScope_2905_; lean_object* v_quotContext_2906_; uint8_t v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2933_; 
v_ref_2904_ = lean_ctor_get(v_a_2891_, 4);
v_currMacroScope_2905_ = lean_ctor_get(v_a_2891_, 9);
v_quotContext_2906_ = lean_ctor_get(v_toCold_2899_, 2);
v___x_2907_ = 0;
v___x_2908_ = l_Lean_SourceInfo_fromRef(v_ref_2904_, v___x_2907_);
v___x_2909_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__0));
v___x_2910_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__1));
lean_inc_n(v___x_2908_, 8);
v___x_2911_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2908_);
lean_ctor_set(v___x_2911_, 1, v___x_2909_);
v___x_2912_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_2913_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__2));
v___x_2914_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__3));
v___x_2915_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2908_);
lean_ctor_set(v___x_2915_, 1, v___x_2913_);
v___x_2916_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__5, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__5_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__5);
v___x_2917_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__7));
lean_inc(v_currMacroScope_2905_);
lean_inc(v_quotContext_2906_);
v___x_2918_ = l_Lean_addMacroScope(v_quotContext_2906_, v___x_2917_, v_currMacroScope_2905_);
v___x_2919_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__10));
v___x_2920_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2908_);
lean_ctor_set(v___x_2920_, 1, v___x_2916_);
lean_ctor_set(v___x_2920_, 2, v___x_2918_);
lean_ctor_set(v___x_2920_, 3, v___x_2919_);
v___x_2921_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11);
v___x_2922_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2908_);
lean_ctor_set(v___x_2922_, 1, v___x_2912_);
lean_ctor_set(v___x_2922_, 2, v___x_2921_);
v___x_2923_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__11));
v___x_2924_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2908_);
lean_ctor_set(v___x_2924_, 1, v___x_2923_);
v___x_2925_ = l_Lean_Syntax_node4(v___x_2908_, v___x_2914_, v___x_2915_, v___x_2920_, v___x_2922_, v___x_2924_);
v___x_2926_ = l_Array_mkArray1___redArg(v___x_2925_);
v___x_2927_ = l_Array_append___redArg(v___x_2926_, v_a_2900_);
lean_dec(v_a_2900_);
v___x_2928_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2908_);
lean_ctor_set(v___x_2928_, 1, v___x_2912_);
lean_ctor_set(v___x_2928_, 2, v___x_2927_);
v___x_2929_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___closed__12));
v___x_2930_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2908_);
lean_ctor_set(v___x_2930_, 1, v___x_2929_);
v___x_2931_ = l_Lean_Syntax_node3(v___x_2908_, v___x_2910_, v___x_2911_, v___x_2928_, v___x_2930_);
if (v_isShared_2903_ == 0)
{
lean_ctor_set(v___x_2902_, 0, v___x_2931_);
v___x_2933_ = v___x_2902_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v___x_2931_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
else
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2943_; 
v_a_2936_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2938_ = v___x_2898_;
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2898_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2941_; 
if (v_isShared_2939_ == 0)
{
v___x_2941_ = v___x_2938_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_a_2936_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock___boxed(lean_object* v_ctx_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_){
_start:
{
lean_object* v_res_2952_; 
v_res_2952_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock(v_ctx_2944_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_);
lean_dec(v_a_2950_);
lean_dec_ref(v_a_2949_);
lean_dec(v_a_2948_);
lean_dec_ref(v_a_2947_);
lean_dec(v_a_2946_);
lean_dec_ref(v_a_2945_);
lean_dec_ref(v_ctx_2944_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0(lean_object* v_upperBound_2953_, lean_object* v_ctx_2954_, lean_object* v_inst_2955_, lean_object* v_R_2956_, lean_object* v_a_2957_, lean_object* v_b_2958_, lean_object* v_c_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0___redArg(v_upperBound_2953_, v_ctx_2954_, v_a_2957_, v_b_2958_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0___boxed(lean_object* v_upperBound_2968_, lean_object* v_ctx_2969_, lean_object* v_inst_2970_, lean_object* v_R_2971_, lean_object* v_a_2972_, lean_object* v_b_2973_, lean_object* v_c_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock_spec__0(v_upperBound_2968_, v_ctx_2969_, v_inst_2970_, v_R_2971_, v_a_2972_, v_b_2973_, v_c_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
lean_dec(v___y_2978_);
lean_dec_ref(v___y_2977_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec_ref(v_ctx_2969_);
lean_dec(v_upperBound_2968_);
return v_res_2982_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2983_; double v___x_2984_; 
v___x_2983_ = lean_unsigned_to_nat(0u);
v___x_2984_ = lean_float_of_nat(v___x_2983_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg(lean_object* v_cls_2987_, lean_object* v_msg_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
lean_object* v_ref_2994_; lean_object* v___x_2995_; lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3040_; 
v_ref_2994_ = lean_ctor_get(v___y_2991_, 4);
v___x_2995_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__2(v_msg_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_);
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_2998_ = v___x_2995_;
v_isShared_2999_ = v_isSharedCheck_3040_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___x_2995_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3040_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3000_; lean_object* v_traceState_3001_; lean_object* v_env_3002_; lean_object* v_nextMacroScope_3003_; lean_object* v_ngen_3004_; lean_object* v_auxDeclNGen_3005_; lean_object* v_cache_3006_; lean_object* v_messages_3007_; lean_object* v_infoState_3008_; lean_object* v_snapshotTasks_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3039_; 
v___x_3000_ = lean_st_ref_take(v___y_2992_);
v_traceState_3001_ = lean_ctor_get(v___x_3000_, 4);
v_env_3002_ = lean_ctor_get(v___x_3000_, 0);
v_nextMacroScope_3003_ = lean_ctor_get(v___x_3000_, 1);
v_ngen_3004_ = lean_ctor_get(v___x_3000_, 2);
v_auxDeclNGen_3005_ = lean_ctor_get(v___x_3000_, 3);
v_cache_3006_ = lean_ctor_get(v___x_3000_, 5);
v_messages_3007_ = lean_ctor_get(v___x_3000_, 6);
v_infoState_3008_ = lean_ctor_get(v___x_3000_, 7);
v_snapshotTasks_3009_ = lean_ctor_get(v___x_3000_, 8);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3011_ = v___x_3000_;
v_isShared_3012_ = v_isSharedCheck_3039_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_snapshotTasks_3009_);
lean_inc(v_infoState_3008_);
lean_inc(v_messages_3007_);
lean_inc(v_cache_3006_);
lean_inc(v_traceState_3001_);
lean_inc(v_auxDeclNGen_3005_);
lean_inc(v_ngen_3004_);
lean_inc(v_nextMacroScope_3003_);
lean_inc(v_env_3002_);
lean_dec(v___x_3000_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3039_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
uint64_t v_tid_3013_; lean_object* v_traces_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3038_; 
v_tid_3013_ = lean_ctor_get_uint64(v_traceState_3001_, sizeof(void*)*1);
v_traces_3014_ = lean_ctor_get(v_traceState_3001_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v_traceState_3001_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3016_ = v_traceState_3001_;
v_isShared_3017_ = v_isSharedCheck_3038_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_traces_3014_);
lean_dec(v_traceState_3001_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3038_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3018_; double v___x_3019_; uint8_t v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3028_; 
v___x_3018_ = lean_box(0);
v___x_3019_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___closed__0);
v___x_3020_ = 0;
v___x_3021_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__22));
v___x_3022_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3022_, 0, v_cls_2987_);
lean_ctor_set(v___x_3022_, 1, v___x_3018_);
lean_ctor_set(v___x_3022_, 2, v___x_3021_);
lean_ctor_set_float(v___x_3022_, sizeof(void*)*3, v___x_3019_);
lean_ctor_set_float(v___x_3022_, sizeof(void*)*3 + 8, v___x_3019_);
lean_ctor_set_uint8(v___x_3022_, sizeof(void*)*3 + 16, v___x_3020_);
v___x_3023_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___closed__1));
v___x_3024_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3022_);
lean_ctor_set(v___x_3024_, 1, v_a_2996_);
lean_ctor_set(v___x_3024_, 2, v___x_3023_);
lean_inc(v_ref_2994_);
v___x_3025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3025_, 0, v_ref_2994_);
lean_ctor_set(v___x_3025_, 1, v___x_3024_);
v___x_3026_ = l_Lean_PersistentArray_push___redArg(v_traces_3014_, v___x_3025_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 0, v___x_3026_);
v___x_3028_ = v___x_3016_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v___x_3026_);
lean_ctor_set_uint64(v_reuseFailAlloc_3037_, sizeof(void*)*1, v_tid_3013_);
v___x_3028_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
lean_object* v___x_3030_; 
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 4, v___x_3028_);
v___x_3030_ = v___x_3011_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_env_3002_);
lean_ctor_set(v_reuseFailAlloc_3036_, 1, v_nextMacroScope_3003_);
lean_ctor_set(v_reuseFailAlloc_3036_, 2, v_ngen_3004_);
lean_ctor_set(v_reuseFailAlloc_3036_, 3, v_auxDeclNGen_3005_);
lean_ctor_set(v_reuseFailAlloc_3036_, 4, v___x_3028_);
lean_ctor_set(v_reuseFailAlloc_3036_, 5, v_cache_3006_);
lean_ctor_set(v_reuseFailAlloc_3036_, 6, v_messages_3007_);
lean_ctor_set(v_reuseFailAlloc_3036_, 7, v_infoState_3008_);
lean_ctor_set(v_reuseFailAlloc_3036_, 8, v_snapshotTasks_3009_);
v___x_3030_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3034_; 
v___x_3031_ = lean_st_ref_put(v___y_2992_, v___x_3030_);
v___x_3032_ = lean_box(0);
if (v_isShared_2999_ == 0)
{
lean_ctor_set(v___x_2998_, 0, v___x_3032_);
v___x_3034_ = v___x_2998_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3032_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg___boxed(lean_object* v_cls_3041_, lean_object* v_msg_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
lean_object* v_res_3048_; 
v_res_3048_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg(v_cls_3041_, v_msg_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3045_);
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3043_);
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__0(lean_object* v_a_3049_, lean_object* v_a_3050_){
_start:
{
if (lean_obj_tag(v_a_3049_) == 0)
{
lean_object* v___x_3051_; 
v___x_3051_ = l_List_reverse___redArg(v_a_3050_);
return v___x_3051_;
}
else
{
lean_object* v_head_3052_; lean_object* v_tail_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3062_; 
v_head_3052_ = lean_ctor_get(v_a_3049_, 0);
v_tail_3053_ = lean_ctor_get(v_a_3049_, 1);
v_isSharedCheck_3062_ = !lean_is_exclusive(v_a_3049_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3055_ = v_a_3049_;
v_isShared_3056_ = v_isSharedCheck_3062_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_tail_3053_);
lean_inc(v_head_3052_);
lean_dec(v_a_3049_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3062_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3057_; lean_object* v___x_3059_; 
v___x_3057_ = l_Lean_MessageData_ofSyntax(v_head_3052_);
if (v_isShared_3056_ == 0)
{
lean_ctor_set(v___x_3055_, 1, v_a_3050_);
lean_ctor_set(v___x_3055_, 0, v___x_3057_);
v___x_3059_ = v___x_3055_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3057_);
lean_ctor_set(v_reuseFailAlloc_3061_, 1, v_a_3050_);
v___x_3059_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
v_a_3049_ = v_tail_3053_;
v_a_3050_ = v___x_3059_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3(void){
_start:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3070_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__0));
v___x_3071_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__2));
v___x_3072_ = l_Lean_Name_append(v___x_3071_, v___x_3070_);
return v___x_3072_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5(void){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3074_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__4));
v___x_3075_ = l_Lean_stringToMessageData(v___x_3074_);
return v___x_3075_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__17(void){
_start:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3103_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__16));
v___x_3104_ = l_String_toRawSubstring_x27(v___x_3103_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds(lean_object* v_declName_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_, lean_object* v_a_3114_){
_start:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v_cmds_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v_toCold_3123_; lean_object* v_options_3124_; lean_object* v___y_3125_; uint8_t v___x_3156_; lean_object* v___x_3157_; 
v___x_3116_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader___closed__0));
v___x_3117_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__1_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_));
v___x_3156_ = 0;
lean_inc(v_declName_3108_);
v___x_3157_ = l_Lean_Elab_Deriving_mkContext(v___x_3116_, v___x_3117_, v_declName_3108_, v___x_3156_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v_a_3158_; lean_object* v___x_3159_; 
v_a_3158_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_a_3158_);
lean_dec_ref_known(v___x_3157_, 1);
v___x_3159_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMutualBlock(v_a_3158_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_a_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; uint8_t v___x_3164_; lean_object* v___x_3165_; 
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
lean_inc(v_a_3160_);
lean_dec_ref_known(v___x_3159_, 1);
v___x_3161_ = lean_unsigned_to_nat(1u);
v___x_3162_ = lean_mk_empty_array_with_capacity(v___x_3161_);
lean_inc_ref(v___x_3162_);
v___x_3163_ = lean_array_push(v___x_3162_, v_declName_3108_);
v___x_3164_ = 1;
lean_inc(v_a_3158_);
v___x_3165_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_a_3158_, v___x_3116_, v___x_3163_, v___x_3164_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_, v_a_3114_);
lean_dec_ref(v___x_3163_);
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_object* v_a_3166_; lean_object* v_instName_3167_; uint8_t v_usePartial_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; 
v_a_3166_ = lean_ctor_get(v___x_3165_, 0);
lean_inc(v_a_3166_);
lean_dec_ref_known(v___x_3165_, 1);
v_instName_3167_ = lean_ctor_get(v_a_3158_, 0);
lean_inc(v_instName_3167_);
v_usePartial_3168_ = lean_ctor_get_uint8(v_a_3158_, sizeof(void*)*3);
lean_dec(v_a_3158_);
v___x_3169_ = lean_array_push(v___x_3162_, v_a_3160_);
v___x_3170_ = l_Array_append___redArg(v___x_3169_, v_a_3166_);
lean_dec(v_a_3166_);
if (v_usePartial_3168_ == 0)
{
lean_object* v_toCold_3171_; lean_object* v_options_3172_; lean_object* v_ref_3173_; lean_object* v_currMacroScope_3174_; lean_object* v_quotContext_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v_toCold_3171_ = lean_ctor_get(v_a_3113_, 0);
v_options_3172_ = lean_ctor_get(v_a_3113_, 1);
v_ref_3173_ = lean_ctor_get(v_a_3113_, 4);
v_currMacroScope_3174_ = lean_ctor_get(v_a_3113_, 9);
v_quotContext_3175_ = lean_ctor_get(v_toCold_3171_, 2);
v___x_3176_ = l_Lean_SourceInfo_fromRef(v_ref_3173_, v_usePartial_3168_);
v___x_3177_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__6));
v___x_3178_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__7));
lean_inc_n(v___x_3176_, 10);
v___x_3179_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3176_);
lean_ctor_set(v___x_3179_, 1, v___x_3177_);
v___x_3180_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__8));
v___x_3181_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3176_);
lean_ctor_set(v___x_3181_, 1, v___x_3180_);
v___x_3182_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_3183_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__10));
v___x_3184_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__12));
v___x_3185_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11);
v___x_3186_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3176_);
lean_ctor_set(v___x_3186_, 1, v___x_3182_);
lean_ctor_set(v___x_3186_, 2, v___x_3185_);
lean_inc_ref(v___x_3186_);
v___x_3187_ = l_Lean_Syntax_node1(v___x_3176_, v___x_3184_, v___x_3186_);
v___x_3188_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__15));
v___x_3189_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__17, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__17_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__17);
v___x_3190_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__18));
lean_inc(v_currMacroScope_3174_);
lean_inc(v_quotContext_3175_);
v___x_3191_ = l_Lean_addMacroScope(v_quotContext_3175_, v___x_3190_, v_currMacroScope_3174_);
v___x_3192_ = lean_box(0);
v___x_3193_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3193_, 0, v___x_3176_);
lean_ctor_set(v___x_3193_, 1, v___x_3189_);
lean_ctor_set(v___x_3193_, 2, v___x_3191_);
lean_ctor_set(v___x_3193_, 3, v___x_3192_);
v___x_3194_ = l_Lean_Syntax_node2(v___x_3176_, v___x_3188_, v___x_3193_, v___x_3186_);
v___x_3195_ = l_Lean_Syntax_node2(v___x_3176_, v___x_3183_, v___x_3187_, v___x_3194_);
v___x_3196_ = l_Lean_Syntax_node1(v___x_3176_, v___x_3182_, v___x_3195_);
v___x_3197_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__19));
v___x_3198_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3176_);
lean_ctor_set(v___x_3198_, 1, v___x_3197_);
v___x_3199_ = l_Lean_mkIdent(v_instName_3167_);
v___x_3200_ = l_Lean_Syntax_node1(v___x_3176_, v___x_3182_, v___x_3199_);
v___x_3201_ = l_Lean_Syntax_node5(v___x_3176_, v___x_3178_, v___x_3179_, v___x_3181_, v___x_3196_, v___x_3198_, v___x_3200_);
v___x_3202_ = lean_array_push(v___x_3170_, v___x_3201_);
lean_inc_ref(v_toCold_3171_);
v_cmds_3119_ = v___x_3202_;
v___y_3120_ = v_a_3111_;
v___y_3121_ = v_a_3112_;
v___y_3122_ = v_a_3113_;
v_toCold_3123_ = v_toCold_3171_;
v_options_3124_ = v_options_3172_;
v___y_3125_ = v_a_3114_;
goto v___jp_3118_;
}
else
{
lean_object* v_toCold_3203_; lean_object* v_options_3204_; 
lean_dec(v_instName_3167_);
v_toCold_3203_ = lean_ctor_get(v_a_3113_, 0);
v_options_3204_ = lean_ctor_get(v_a_3113_, 1);
lean_inc_ref(v_toCold_3203_);
v_cmds_3119_ = v___x_3170_;
v___y_3120_ = v_a_3111_;
v___y_3121_ = v_a_3112_;
v___y_3122_ = v_a_3113_;
v_toCold_3123_ = v_toCold_3203_;
v_options_3124_ = v_options_3204_;
v___y_3125_ = v_a_3114_;
goto v___jp_3118_;
}
}
else
{
lean_object* v_a_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3212_; 
lean_dec_ref(v___x_3162_);
lean_dec(v_a_3160_);
lean_dec(v_a_3158_);
v_a_3205_ = lean_ctor_get(v___x_3165_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3165_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3207_ = v___x_3165_;
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_a_3205_);
lean_dec(v___x_3165_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3210_; 
if (v_isShared_3208_ == 0)
{
v___x_3210_ = v___x_3207_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_a_3205_);
v___x_3210_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
return v___x_3210_;
}
}
}
}
else
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3220_; 
lean_dec(v_a_3158_);
lean_dec(v_declName_3108_);
v_a_3213_ = lean_ctor_get(v___x_3159_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3215_ = v___x_3159_;
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_3159_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3218_; 
if (v_isShared_3216_ == 0)
{
v___x_3218_ = v___x_3215_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3213_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
}
else
{
lean_object* v_a_3221_; lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3228_; 
lean_dec(v_declName_3108_);
v_a_3221_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3228_ == 0)
{
v___x_3223_ = v___x_3157_;
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
else
{
lean_inc(v_a_3221_);
lean_dec(v___x_3157_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3228_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3226_; 
if (v_isShared_3224_ == 0)
{
v___x_3226_ = v___x_3223_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_a_3221_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
v___jp_3118_:
{
uint8_t v_hasTrace_3126_; 
v_hasTrace_3126_ = lean_ctor_get_uint8(v_options_3124_, sizeof(void*)*1);
if (v_hasTrace_3126_ == 0)
{
lean_object* v___x_3127_; 
lean_dec_ref(v_toCold_3123_);
v___x_3127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3127_, 0, v_cmds_3119_);
return v___x_3127_;
}
else
{
lean_object* v_inheritedTraceOptions_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; uint8_t v___x_3131_; 
v_inheritedTraceOptions_3128_ = lean_ctor_get(v_toCold_3123_, 4);
lean_inc_ref(v_inheritedTraceOptions_3128_);
lean_dec_ref(v_toCold_3123_);
v___x_3129_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__0));
v___x_3130_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3);
v___x_3131_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3128_, v_options_3124_, v___x_3130_);
lean_dec_ref(v_inheritedTraceOptions_3128_);
if (v___x_3131_ == 0)
{
lean_object* v___x_3132_; 
v___x_3132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3132_, 0, v_cmds_3119_);
return v___x_3132_;
}
else
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3133_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5);
lean_inc_ref(v_cmds_3119_);
v___x_3134_ = lean_array_to_list(v_cmds_3119_);
v___x_3135_ = lean_box(0);
v___x_3136_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__0(v___x_3134_, v___x_3135_);
v___x_3137_ = l_Lean_MessageData_ofList(v___x_3136_);
v___x_3138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3133_);
lean_ctor_set(v___x_3138_, 1, v___x_3137_);
v___x_3139_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg(v___x_3129_, v___x_3138_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3125_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3146_; 
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3146_ == 0)
{
lean_object* v_unused_3147_; 
v_unused_3147_ = lean_ctor_get(v___x_3139_, 0);
lean_dec(v_unused_3147_);
v___x_3141_ = v___x_3139_;
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
else
{
lean_dec(v___x_3139_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3144_; 
if (v_isShared_3142_ == 0)
{
lean_ctor_set(v___x_3141_, 0, v_cmds_3119_);
v___x_3144_ = v___x_3141_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_cmds_3119_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
lean_dec_ref(v_cmds_3119_);
v_a_3148_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___x_3139_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3139_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3153_; 
if (v_isShared_3151_ == 0)
{
v___x_3153_ = v___x_3150_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3148_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___boxed(lean_object* v_declName_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_){
_start:
{
lean_object* v_res_3237_; 
v_res_3237_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds(v_declName_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_);
lean_dec(v_a_3235_);
lean_dec_ref(v_a_3234_);
lean_dec(v_a_3233_);
lean_dec_ref(v_a_3232_);
lean_dec(v_a_3231_);
lean_dec_ref(v_a_3230_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1(lean_object* v_cls_3238_, lean_object* v_msg_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
lean_object* v___x_3247_; 
v___x_3247_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg(v_cls_3238_, v_msg_3239_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___boxed(lean_object* v_cls_3248_, lean_object* v_msg_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_){
_start:
{
lean_object* v_res_3257_; 
v_res_3257_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1(v_cls_3248_, v_msg_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
return v_res_3257_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__3(void){
_start:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3265_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__2));
v___x_3266_ = l_String_toRawSubstring_x27(v___x_3265_);
return v___x_3266_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__6(void){
_start:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3270_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__5));
v___x_3271_ = l_String_toRawSubstring_x27(v___x_3270_);
return v___x_3271_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__12(void){
_start:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3284_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__11));
v___x_3285_ = l_String_toRawSubstring_x27(v___x_3284_);
return v___x_3285_;
}
}
static lean_object* _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__16(void){
_start:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3291_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__15));
v___x_3292_ = l_String_toRawSubstring_x27(v___x_3291_);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg(lean_object* v_ctx_3296_, lean_object* v_name_3297_, lean_object* v_a_3298_){
_start:
{
lean_object* v_toCold_3300_; lean_object* v_auxFunNames_3301_; lean_object* v_ref_3302_; lean_object* v_currMacroScope_3303_; lean_object* v_quotContext_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v_auxFunName_3307_; uint8_t v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
v_toCold_3300_ = lean_ctor_get(v_a_3298_, 0);
v_auxFunNames_3301_ = lean_ctor_get(v_ctx_3296_, 2);
v_ref_3302_ = lean_ctor_get(v_a_3298_, 4);
v_currMacroScope_3303_ = lean_ctor_get(v_a_3298_, 9);
v_quotContext_3304_ = lean_ctor_get(v_toCold_3300_, 2);
v___x_3305_ = lean_box(0);
v___x_3306_ = lean_unsigned_to_nat(0u);
v_auxFunName_3307_ = lean_array_get_borrowed(v___x_3305_, v_auxFunNames_3301_, v___x_3306_);
v___x_3308_ = 0;
v___x_3309_ = l_Lean_SourceInfo_fromRef(v_ref_3302_, v___x_3308_);
v___x_3310_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__2));
v___x_3311_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__4));
v___x_3312_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__14));
v___x_3313_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__7___redArg___lam__2___closed__11);
lean_inc_n(v___x_3309_, 26);
v___x_3314_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3309_);
lean_ctor_set(v___x_3314_, 1, v___x_3312_);
lean_ctor_set(v___x_3314_, 2, v___x_3313_);
lean_inc_ref_n(v___x_3314_, 12);
v___x_3315_ = l_Lean_Syntax_node7(v___x_3309_, v___x_3311_, v___x_3314_, v___x_3314_, v___x_3314_, v___x_3314_, v___x_3314_, v___x_3314_, v___x_3314_);
v___x_3316_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__6));
v___x_3317_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__7));
v___x_3318_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3309_);
lean_ctor_set(v___x_3318_, 1, v___x_3317_);
v___x_3319_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__9));
lean_inc(v_auxFunName_3307_);
v___x_3320_ = l_Lean_mkIdent(v_auxFunName_3307_);
v___x_3321_ = l_Lean_Syntax_node2(v___x_3309_, v___x_3319_, v___x_3320_, v___x_3314_);
v___x_3322_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__11));
v___x_3323_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__1));
v___x_3324_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__19));
v___x_3325_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3309_);
lean_ctor_set(v___x_3325_, 1, v___x_3324_);
v___x_3326_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__3, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__3_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__3);
v___x_3327_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__4));
lean_inc_n(v_currMacroScope_3303_, 6);
lean_inc_n(v_quotContext_3304_, 6);
v___x_3328_ = l_Lean_addMacroScope(v_quotContext_3304_, v___x_3327_, v_currMacroScope_3303_);
v___x_3329_ = lean_box(0);
v___x_3330_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3309_);
lean_ctor_set(v___x_3330_, 1, v___x_3326_);
lean_ctor_set(v___x_3330_, 2, v___x_3328_);
lean_ctor_set(v___x_3330_, 3, v___x_3329_);
v___x_3331_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__6, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__6_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__6);
v___x_3332_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__7));
v___x_3333_ = l_Lean_addMacroScope(v_quotContext_3304_, v___x_3332_, v_currMacroScope_3303_);
v___x_3334_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3309_);
lean_ctor_set(v___x_3334_, 1, v___x_3331_);
lean_ctor_set(v___x_3334_, 2, v___x_3333_);
lean_ctor_set(v___x_3334_, 3, v___x_3329_);
v___x_3335_ = l_Lean_Syntax_node2(v___x_3309_, v___x_3312_, v___x_3330_, v___x_3334_);
v___x_3336_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__11));
v___x_3337_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3309_);
lean_ctor_set(v___x_3337_, 1, v___x_3336_);
v___x_3338_ = l_Lean_mkCIdent(v_name_3297_);
lean_inc_ref(v___x_3337_);
v___x_3339_ = l_Lean_Syntax_node2(v___x_3309_, v___x_3312_, v___x_3337_, v___x_3338_);
v___x_3340_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__40));
v___x_3341_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3309_);
lean_ctor_set(v___x_3341_, 1, v___x_3340_);
v___x_3342_ = l_Lean_Syntax_node5(v___x_3309_, v___x_3323_, v___x_3325_, v___x_3335_, v___x_3339_, v___x_3314_, v___x_3341_);
v___x_3343_ = l_Lean_Syntax_node1(v___x_3309_, v___x_3312_, v___x_3342_);
v___x_3344_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__13));
v___x_3345_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__14);
v___x_3346_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__15));
v___x_3347_ = l_Lean_addMacroScope(v_quotContext_3304_, v___x_3346_, v_currMacroScope_3303_);
v___x_3348_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__10));
v___x_3349_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3309_);
lean_ctor_set(v___x_3349_, 1, v___x_3345_);
lean_ctor_set(v___x_3349_, 2, v___x_3347_);
lean_ctor_set(v___x_3349_, 3, v___x_3348_);
v___x_3350_ = l_Lean_Syntax_node2(v___x_3309_, v___x_3344_, v___x_3337_, v___x_3349_);
v___x_3351_ = l_Lean_Syntax_node1(v___x_3309_, v___x_3312_, v___x_3350_);
v___x_3352_ = l_Lean_Syntax_node2(v___x_3309_, v___x_3322_, v___x_3343_, v___x_3351_);
v___x_3353_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__21));
v___x_3354_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__22));
v___x_3355_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3309_);
lean_ctor_set(v___x_3355_, 1, v___x_3354_);
v___x_3356_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__3));
v___x_3357_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__35);
v___x_3358_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__2___redArg___lam__0___closed__36));
v___x_3359_ = l_Lean_addMacroScope(v_quotContext_3304_, v___x_3358_, v_currMacroScope_3303_);
v___x_3360_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchNew___closed__13));
v___x_3361_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3309_);
lean_ctor_set(v___x_3361_, 1, v___x_3357_);
lean_ctor_set(v___x_3361_, 2, v___x_3359_);
lean_ctor_set(v___x_3361_, 3, v___x_3360_);
v___x_3362_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__12, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__12_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__12);
v___x_3363_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__14));
v___x_3364_ = l_Lean_addMacroScope(v_quotContext_3304_, v___x_3363_, v_currMacroScope_3303_);
v___x_3365_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3309_);
lean_ctor_set(v___x_3365_, 1, v___x_3362_);
lean_ctor_set(v___x_3365_, 2, v___x_3364_);
lean_ctor_set(v___x_3365_, 3, v___x_3329_);
v___x_3366_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__16, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__16_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__16);
v___x_3367_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___closed__17));
v___x_3368_ = l_Lean_addMacroScope(v_quotContext_3304_, v___x_3367_, v_currMacroScope_3303_);
v___x_3369_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3309_);
lean_ctor_set(v___x_3369_, 1, v___x_3366_);
lean_ctor_set(v___x_3369_, 2, v___x_3368_);
lean_ctor_set(v___x_3369_, 3, v___x_3329_);
v___x_3370_ = l_Lean_Syntax_node2(v___x_3309_, v___x_3312_, v___x_3365_, v___x_3369_);
v___x_3371_ = l_Lean_Syntax_node2(v___x_3309_, v___x_3356_, v___x_3361_, v___x_3370_);
v___x_3372_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkAuxFunction___closed__25));
v___x_3373_ = l_Lean_Syntax_node2(v___x_3309_, v___x_3372_, v___x_3314_, v___x_3314_);
v___x_3374_ = l_Lean_Syntax_node4(v___x_3309_, v___x_3353_, v___x_3355_, v___x_3371_, v___x_3373_, v___x_3314_);
v___x_3375_ = l_Lean_Syntax_node5(v___x_3309_, v___x_3316_, v___x_3318_, v___x_3321_, v___x_3352_, v___x_3374_, v___x_3314_);
v___x_3376_ = l_Lean_Syntax_node2(v___x_3309_, v___x_3310_, v___x_3315_, v___x_3375_);
v___x_3377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3376_);
return v___x_3377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg___boxed(lean_object* v_ctx_3378_, lean_object* v_name_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_){
_start:
{
lean_object* v_res_3382_; 
v_res_3382_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg(v_ctx_3378_, v_name_3379_, v_a_3380_);
lean_dec_ref(v_a_3380_);
lean_dec_ref(v_ctx_3378_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun(lean_object* v_ctx_3383_, lean_object* v_name_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_){
_start:
{
lean_object* v___x_3392_; 
v___x_3392_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg(v_ctx_3383_, v_name_3384_, v_a_3389_);
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___boxed(lean_object* v_ctx_3393_, lean_object* v_name_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_, lean_object* v_a_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_){
_start:
{
lean_object* v_res_3402_; 
v_res_3402_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun(v_ctx_3393_, v_name_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_, v_a_3399_, v_a_3400_);
lean_dec(v_a_3400_);
lean_dec_ref(v_a_3399_);
lean_dec(v_a_3398_);
lean_dec_ref(v_a_3397_);
lean_dec(v_a_3396_);
lean_dec_ref(v_a_3395_);
lean_dec_ref(v_ctx_3393_);
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumCmd(lean_object* v_name_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_){
_start:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; uint8_t v___x_3413_; lean_object* v___x_3414_; 
v___x_3411_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader___closed__0));
v___x_3412_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__initFn___closed__1_00___x40_Lean_Elab_Deriving_Ord_957574035____hygCtx___hyg_4_));
v___x_3413_ = 1;
lean_inc(v_name_3403_);
v___x_3414_ = l_Lean_Elab_Deriving_mkContext(v___x_3411_, v___x_3412_, v_name_3403_, v___x_3413_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_);
if (lean_obj_tag(v___x_3414_) == 0)
{
lean_object* v_a_3415_; lean_object* v___x_3416_; lean_object* v_a_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; 
v_a_3415_ = lean_ctor_get(v___x_3414_, 0);
lean_inc(v_a_3415_);
lean_dec_ref_known(v___x_3414_, 1);
lean_inc(v_name_3403_);
v___x_3416_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumFun___redArg(v_a_3415_, v_name_3403_, v_a_3408_);
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
lean_inc(v_a_3417_);
lean_dec_ref(v___x_3416_);
v___x_3418_ = lean_unsigned_to_nat(1u);
v___x_3419_ = lean_mk_empty_array_with_capacity(v___x_3418_);
lean_inc_ref(v___x_3419_);
v___x_3420_ = lean_array_push(v___x_3419_, v_name_3403_);
v___x_3421_ = l_Lean_Elab_Deriving_mkInstanceCmds(v_a_3415_, v___x_3411_, v___x_3420_, v___x_3413_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_);
lean_dec_ref(v___x_3420_);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v_options_3422_; lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3464_; 
v_options_3422_ = lean_ctor_get(v_a_3408_, 1);
v_a_3423_ = lean_ctor_get(v___x_3421_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3425_ = v___x_3421_;
v_isShared_3426_ = v_isSharedCheck_3464_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3421_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3464_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v_toCold_3427_; uint8_t v_hasTrace_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; 
v_toCold_3427_ = lean_ctor_get(v_a_3408_, 0);
v_hasTrace_3428_ = lean_ctor_get_uint8(v_options_3422_, sizeof(void*)*1);
v___x_3429_ = lean_array_push(v___x_3419_, v_a_3417_);
v___x_3430_ = l_Array_append___redArg(v___x_3429_, v_a_3423_);
lean_dec(v_a_3423_);
if (v_hasTrace_3428_ == 0)
{
lean_object* v___x_3432_; 
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 0, v___x_3430_);
v___x_3432_ = v___x_3425_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v___x_3430_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; uint8_t v___x_3437_; 
v_inheritedTraceOptions_3434_ = lean_ctor_get(v_toCold_3427_, 4);
v___x_3435_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__0));
v___x_3436_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__3);
v___x_3437_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3434_, v_options_3422_, v___x_3436_);
if (v___x_3437_ == 0)
{
lean_object* v___x_3439_; 
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 0, v___x_3430_);
v___x_3439_ = v___x_3425_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v___x_3430_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
else
{
lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; 
lean_del_object(v___x_3425_);
v___x_3441_ = lean_obj_once(&l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5, &l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5_once, _init_l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__5);
lean_inc_ref(v___x_3430_);
v___x_3442_ = lean_array_to_list(v___x_3430_);
v___x_3443_ = lean_box(0);
v___x_3444_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__0(v___x_3442_, v___x_3443_);
v___x_3445_ = l_Lean_MessageData_ofList(v___x_3444_);
v___x_3446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3441_);
lean_ctor_set(v___x_3446_, 1, v___x_3445_);
v___x_3447_ = l_Lean_addTrace___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds_spec__1___redArg(v___x_3435_, v___x_3446_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_);
if (lean_obj_tag(v___x_3447_) == 0)
{
lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3454_ == 0)
{
lean_object* v_unused_3455_; 
v_unused_3455_ = lean_ctor_get(v___x_3447_, 0);
lean_dec(v_unused_3455_);
v___x_3449_ = v___x_3447_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_dec(v___x_3447_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 0, v___x_3430_);
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___x_3430_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
else
{
lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3463_; 
lean_dec_ref(v___x_3430_);
v_a_3456_ = lean_ctor_get(v___x_3447_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3447_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3458_ = v___x_3447_;
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3447_);
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
}
}
}
else
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3472_; 
lean_dec_ref(v___x_3419_);
lean_dec(v_a_3417_);
v_a_3465_ = lean_ctor_get(v___x_3421_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3467_ = v___x_3421_;
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3421_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3470_; 
if (v_isShared_3468_ == 0)
{
v___x_3470_ = v___x_3467_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_a_3465_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
else
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3480_; 
lean_dec(v_name_3403_);
v_a_3473_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3475_ = v___x_3414_;
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3414_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3478_; 
if (v_isShared_3476_ == 0)
{
v___x_3478_ = v___x_3475_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumCmd___boxed(lean_object* v_name_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_){
_start:
{
lean_object* v_res_3489_; 
v_res_3489_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumCmd(v_name_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
lean_dec(v_a_3487_);
lean_dec_ref(v_a_3486_);
lean_dec(v_a_3485_);
lean_dec_ref(v_a_3484_);
lean_dec(v_a_3483_);
lean_dec_ref(v_a_3482_);
return v_res_3489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__0(uint8_t v_a_3490_, lean_object* v_declName_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_){
_start:
{
if (v_a_3490_ == 0)
{
lean_object* v___x_3499_; 
v___x_3499_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds(v_declName_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_);
return v___x_3499_;
}
else
{
lean_object* v___x_3500_; 
v___x_3500_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdEnumCmd(v_declName_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_);
return v___x_3500_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__0___boxed(lean_object* v_a_3501_, lean_object* v_declName_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
uint8_t v_a_3783__boxed_3510_; lean_object* v_res_3511_; 
v_a_3783__boxed_3510_ = lean_unbox(v_a_3501_);
v_res_3511_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__0(v_a_3783__boxed_3510_, v_declName_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec(v___y_3504_);
lean_dec_ref(v___y_3503_);
return v_res_3511_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_3512_; 
v___x_3512_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3512_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3513_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__0);
v___x_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3513_);
return v___x_3514_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3515_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1);
v___x_3516_ = lean_unsigned_to_nat(0u);
v___x_3517_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_3517_, 0, v___x_3516_);
lean_ctor_set(v___x_3517_, 1, v___x_3516_);
lean_ctor_set(v___x_3517_, 2, v___x_3516_);
lean_ctor_set(v___x_3517_, 3, v___x_3516_);
lean_ctor_set(v___x_3517_, 4, v___x_3515_);
lean_ctor_set(v___x_3517_, 5, v___x_3515_);
lean_ctor_set(v___x_3517_, 6, v___x_3515_);
lean_ctor_set(v___x_3517_, 7, v___x_3515_);
lean_ctor_set(v___x_3517_, 8, v___x_3515_);
lean_ctor_set(v___x_3517_, 9, v___x_3515_);
lean_ctor_set(v___x_3517_, 10, v___x_3515_);
return v___x_3517_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3518_ = lean_unsigned_to_nat(32u);
v___x_3519_ = lean_mk_empty_array_with_capacity(v___x_3518_);
v___x_3520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3519_);
return v___x_3520_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3521_ = ((size_t)5ULL);
v___x_3522_ = lean_unsigned_to_nat(0u);
v___x_3523_ = lean_unsigned_to_nat(32u);
v___x_3524_ = lean_mk_empty_array_with_capacity(v___x_3523_);
v___x_3525_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__3);
v___x_3526_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3526_, 0, v___x_3525_);
lean_ctor_set(v___x_3526_, 1, v___x_3524_);
lean_ctor_set(v___x_3526_, 2, v___x_3522_);
lean_ctor_set(v___x_3526_, 3, v___x_3522_);
lean_ctor_set_usize(v___x_3526_, 4, v___x_3521_);
return v___x_3526_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3527_ = lean_box(1);
v___x_3528_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__4);
v___x_3529_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__1);
v___x_3530_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3529_);
lean_ctor_set(v___x_3530_, 1, v___x_3528_);
lean_ctor_set(v___x_3530_, 2, v___x_3527_);
return v___x_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(lean_object* v_msgData_3531_, lean_object* v___y_3532_){
_start:
{
lean_object* v___x_3534_; lean_object* v_env_3535_; lean_object* v___x_3536_; lean_object* v_scopes_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v_opts_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3534_ = lean_st_ref_get(v___y_3532_);
v_env_3535_ = lean_ctor_get(v___x_3534_, 0);
lean_inc_ref(v_env_3535_);
lean_dec(v___x_3534_);
v___x_3536_ = lean_st_ref_get(v___y_3532_);
v_scopes_3537_ = lean_ctor_get(v___x_3536_, 2);
lean_inc(v_scopes_3537_);
lean_dec(v___x_3536_);
v___x_3538_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3539_ = l_List_head_x21___redArg(v___x_3538_, v_scopes_3537_);
lean_dec(v_scopes_3537_);
v_opts_3540_ = lean_ctor_get(v___x_3539_, 1);
lean_inc_ref(v_opts_3540_);
lean_dec(v___x_3539_);
v___x_3541_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2);
v___x_3542_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5);
v___x_3543_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3543_, 0, v_env_3535_);
lean_ctor_set(v___x_3543_, 1, v___x_3541_);
lean_ctor_set(v___x_3543_, 2, v___x_3542_);
lean_ctor_set(v___x_3543_, 3, v_opts_3540_);
v___x_3544_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3543_);
lean_ctor_set(v___x_3544_, 1, v_msgData_3531_);
v___x_3545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3544_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___boxed(lean_object* v_msgData_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
lean_object* v_res_3549_; 
v_res_3549_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_msgData_3546_, v___y_3547_);
lean_dec(v___y_3547_);
return v_res_3549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11___redArg(lean_object* v_msgData_3550_, lean_object* v_macroStack_3551_, lean_object* v___y_3552_){
_start:
{
lean_object* v___x_3554_; lean_object* v_scopes_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v_opts_3558_; lean_object* v___x_3559_; uint8_t v___x_3560_; 
v___x_3554_ = lean_st_ref_get(v___y_3552_);
v_scopes_3555_ = lean_ctor_get(v___x_3554_, 2);
lean_inc(v_scopes_3555_);
lean_dec(v___x_3554_);
v___x_3556_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_3557_ = l_List_head_x21___redArg(v___x_3556_, v_scopes_3555_);
lean_dec(v_scopes_3555_);
v_opts_3558_ = lean_ctor_get(v___x_3557_, 1);
lean_inc_ref(v_opts_3558_);
lean_dec(v___x_3557_);
v___x_3559_ = l_Lean_Elab_pp_macroStack;
v___x_3560_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__11(v_opts_3558_, v___x_3559_);
lean_dec_ref(v_opts_3558_);
if (v___x_3560_ == 0)
{
lean_object* v___x_3561_; 
lean_dec(v_macroStack_3551_);
v___x_3561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3561_, 0, v_msgData_3550_);
return v___x_3561_;
}
else
{
if (lean_obj_tag(v_macroStack_3551_) == 0)
{
lean_object* v___x_3562_; 
v___x_3562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3562_, 0, v_msgData_3550_);
return v___x_3562_;
}
else
{
lean_object* v_head_3563_; lean_object* v_after_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3579_; 
v_head_3563_ = lean_ctor_get(v_macroStack_3551_, 0);
lean_inc(v_head_3563_);
v_after_3564_ = lean_ctor_get(v_head_3563_, 1);
v_isSharedCheck_3579_ = !lean_is_exclusive(v_head_3563_);
if (v_isSharedCheck_3579_ == 0)
{
lean_object* v_unused_3580_; 
v_unused_3580_ = lean_ctor_get(v_head_3563_, 0);
lean_dec(v_unused_3580_);
v___x_3566_ = v_head_3563_;
v_isShared_3567_ = v_isSharedCheck_3579_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_after_3564_);
lean_dec(v_head_3563_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3579_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3568_; lean_object* v___x_3570_; 
v___x_3568_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12___closed__0);
if (v_isShared_3567_ == 0)
{
lean_ctor_set_tag(v___x_3566_, 7);
lean_ctor_set(v___x_3566_, 1, v___x_3568_);
lean_ctor_set(v___x_3566_, 0, v_msgData_3550_);
v___x_3570_ = v___x_3566_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_msgData_3550_);
lean_ctor_set(v_reuseFailAlloc_3578_, 1, v___x_3568_);
v___x_3570_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v_msgData_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3571_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3___redArg___closed__2);
v___x_3572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3570_);
lean_ctor_set(v___x_3572_, 1, v___x_3571_);
v___x_3573_ = l_Lean_MessageData_ofSyntax(v_after_3564_);
v___x_3574_ = l_Lean_indentD(v___x_3573_);
v_msgData_3575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_3575_, 0, v___x_3572_);
lean_ctor_set(v_msgData_3575_, 1, v___x_3574_);
v___x_3576_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0_spec__0_spec__3_spec__12(v_msgData_3575_, v_macroStack_3551_);
v___x_3577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3576_);
return v___x_3577_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11___redArg___boxed(lean_object* v_msgData_3581_, lean_object* v_macroStack_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11___redArg(v_msgData_3581_, v_macroStack_3582_, v___y_3583_);
lean_dec(v___y_3583_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9___redArg(lean_object* v_msg_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_){
_start:
{
lean_object* v___x_3590_; 
v___x_3590_ = l_Lean_Elab_Command_getRef___redArg(v___y_3587_);
if (lean_obj_tag(v___x_3590_) == 0)
{
lean_object* v_a_3591_; lean_object* v_macroStack_3592_; lean_object* v___x_3593_; lean_object* v_a_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v_a_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3605_; 
v_a_3591_ = lean_ctor_get(v___x_3590_, 0);
lean_inc(v_a_3591_);
lean_dec_ref_known(v___x_3590_, 1);
v_macroStack_3592_ = lean_ctor_get(v___y_3587_, 4);
v___x_3593_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_msg_3586_, v___y_3588_);
v_a_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc(v_a_3594_);
lean_dec_ref(v___x_3593_);
v___x_3595_ = l_Lean_Elab_getBetterRef(v_a_3591_, v_macroStack_3592_);
lean_dec(v_a_3591_);
lean_inc(v_macroStack_3592_);
v___x_3596_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11___redArg(v_a_3594_, v_macroStack_3592_, v___y_3588_);
v_a_3597_ = lean_ctor_get(v___x_3596_, 0);
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3599_ = v___x_3596_;
v_isShared_3600_ = v_isSharedCheck_3605_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_a_3597_);
lean_dec(v___x_3596_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3605_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___x_3601_; lean_object* v___x_3603_; 
v___x_3601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3595_);
lean_ctor_set(v___x_3601_, 1, v_a_3597_);
if (v_isShared_3600_ == 0)
{
lean_ctor_set_tag(v___x_3599_, 1);
lean_ctor_set(v___x_3599_, 0, v___x_3601_);
v___x_3603_ = v___x_3599_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v___x_3601_);
v___x_3603_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
return v___x_3603_;
}
}
}
else
{
lean_object* v_a_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3613_; 
lean_dec_ref(v_msg_3586_);
v_a_3606_ = lean_ctor_get(v___x_3590_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3608_ = v___x_3590_;
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_a_3606_);
lean_dec(v___x_3590_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3611_; 
if (v_isShared_3609_ == 0)
{
v___x_3611_ = v___x_3608_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_a_3606_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_msg_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
lean_object* v_res_3618_; 
v_res_3618_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_3614_, v___y_3615_, v___y_3616_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3615_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(lean_object* v_ref_3619_, lean_object* v_msg_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
lean_object* v___x_3624_; 
v___x_3624_ = l_Lean_Elab_Command_getRef___redArg(v___y_3621_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_object* v_a_3625_; lean_object* v_fileName_3626_; lean_object* v_fileMap_3627_; lean_object* v_currRecDepth_3628_; lean_object* v_cmdPos_3629_; lean_object* v_macroStack_3630_; lean_object* v_quotContext_x3f_3631_; lean_object* v_currMacroScope_3632_; lean_object* v_snap_x3f_3633_; lean_object* v_cancelTk_x3f_3634_; uint8_t v_suppressElabErrors_3635_; lean_object* v_ref_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; 
v_a_3625_ = lean_ctor_get(v___x_3624_, 0);
lean_inc(v_a_3625_);
lean_dec_ref_known(v___x_3624_, 1);
v_fileName_3626_ = lean_ctor_get(v___y_3621_, 0);
v_fileMap_3627_ = lean_ctor_get(v___y_3621_, 1);
v_currRecDepth_3628_ = lean_ctor_get(v___y_3621_, 2);
v_cmdPos_3629_ = lean_ctor_get(v___y_3621_, 3);
v_macroStack_3630_ = lean_ctor_get(v___y_3621_, 4);
v_quotContext_x3f_3631_ = lean_ctor_get(v___y_3621_, 5);
v_currMacroScope_3632_ = lean_ctor_get(v___y_3621_, 6);
v_snap_x3f_3633_ = lean_ctor_get(v___y_3621_, 8);
v_cancelTk_x3f_3634_ = lean_ctor_get(v___y_3621_, 9);
v_suppressElabErrors_3635_ = lean_ctor_get_uint8(v___y_3621_, sizeof(void*)*10);
v_ref_3636_ = l_Lean_replaceRef(v_ref_3619_, v_a_3625_);
lean_dec(v_a_3625_);
lean_inc(v_cancelTk_x3f_3634_);
lean_inc(v_snap_x3f_3633_);
lean_inc(v_currMacroScope_3632_);
lean_inc(v_quotContext_x3f_3631_);
lean_inc(v_macroStack_3630_);
lean_inc(v_cmdPos_3629_);
lean_inc(v_currRecDepth_3628_);
lean_inc_ref(v_fileMap_3627_);
lean_inc_ref(v_fileName_3626_);
v___x_3637_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_3637_, 0, v_fileName_3626_);
lean_ctor_set(v___x_3637_, 1, v_fileMap_3627_);
lean_ctor_set(v___x_3637_, 2, v_currRecDepth_3628_);
lean_ctor_set(v___x_3637_, 3, v_cmdPos_3629_);
lean_ctor_set(v___x_3637_, 4, v_macroStack_3630_);
lean_ctor_set(v___x_3637_, 5, v_quotContext_x3f_3631_);
lean_ctor_set(v___x_3637_, 6, v_currMacroScope_3632_);
lean_ctor_set(v___x_3637_, 7, v_ref_3636_);
lean_ctor_set(v___x_3637_, 8, v_snap_x3f_3633_);
lean_ctor_set(v___x_3637_, 9, v_cancelTk_x3f_3634_);
lean_ctor_set_uint8(v___x_3637_, sizeof(void*)*10, v_suppressElabErrors_3635_);
v___x_3638_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_3620_, v___x_3637_, v___y_3622_);
lean_dec_ref_known(v___x_3637_, 10);
return v___x_3638_;
}
else
{
lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3646_; 
lean_dec_ref(v_msg_3620_);
v_a_3639_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3646_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3646_ == 0)
{
v___x_3641_ = v___x_3624_;
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_dec(v___x_3624_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3644_; 
if (v_isShared_3642_ == 0)
{
v___x_3644_ = v___x_3641_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_a_3639_);
v___x_3644_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
return v___x_3644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_ref_3647_, lean_object* v_msg_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_){
_start:
{
lean_object* v_res_3652_; 
v_res_3652_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v_ref_3647_, v_msg_3648_, v___y_3649_, v___y_3650_);
lean_dec(v___y_3650_);
lean_dec_ref(v___y_3649_);
lean_dec(v_ref_3647_);
return v_res_3652_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3654_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__0));
v___x_3655_ = l_Lean_stringToMessageData(v___x_3654_);
return v___x_3655_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3657_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__2));
v___x_3658_ = l_Lean_stringToMessageData(v___x_3657_);
return v___x_3658_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3660_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__4));
v___x_3661_ = l_Lean_stringToMessageData(v___x_3660_);
return v___x_3661_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; 
v___x_3663_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__6));
v___x_3664_ = l_Lean_stringToMessageData(v___x_3663_);
return v___x_3664_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3666_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__8));
v___x_3667_ = l_Lean_stringToMessageData(v___x_3666_);
return v___x_3667_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__11(void){
_start:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; 
v___x_3669_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__10));
v___x_3670_ = l_Lean_stringToMessageData(v___x_3669_);
return v___x_3670_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__13(void){
_start:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3672_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__12));
v___x_3673_ = l_Lean_stringToMessageData(v___x_3672_);
return v___x_3673_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_msg_3674_, lean_object* v_declHint_3675_, lean_object* v___y_3676_){
_start:
{
lean_object* v___x_3678_; lean_object* v_env_3679_; uint8_t v___x_3680_; 
v___x_3678_ = lean_st_ref_get(v___y_3676_);
v_env_3679_ = lean_ctor_get(v___x_3678_, 0);
lean_inc_ref(v_env_3679_);
lean_dec(v___x_3678_);
v___x_3680_ = l_Lean_Name_isAnonymous(v_declHint_3675_);
if (v___x_3680_ == 0)
{
uint8_t v_isExporting_3681_; 
v_isExporting_3681_ = lean_ctor_get_uint8(v_env_3679_, sizeof(void*)*8);
if (v_isExporting_3681_ == 0)
{
lean_object* v___x_3682_; 
lean_dec_ref(v_env_3679_);
lean_dec(v_declHint_3675_);
v___x_3682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3682_, 0, v_msg_3674_);
return v___x_3682_;
}
else
{
lean_object* v___x_3683_; uint8_t v___x_3684_; 
lean_inc_ref(v_env_3679_);
v___x_3683_ = l_Lean_Environment_setExporting(v_env_3679_, v___x_3680_);
lean_inc(v_declHint_3675_);
lean_inc_ref(v___x_3683_);
v___x_3684_ = l_Lean_Environment_contains(v___x_3683_, v_declHint_3675_, v_isExporting_3681_);
if (v___x_3684_ == 0)
{
lean_object* v___x_3685_; 
lean_dec_ref(v___x_3683_);
lean_dec_ref(v_env_3679_);
lean_dec(v_declHint_3675_);
v___x_3685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3685_, 0, v_msg_3674_);
return v___x_3685_;
}
else
{
lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v_c_3691_; lean_object* v___x_3692_; 
v___x_3686_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__2);
v___x_3687_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg___closed__5);
v___x_3688_ = l_Lean_Options_empty;
v___x_3689_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3683_);
lean_ctor_set(v___x_3689_, 1, v___x_3686_);
lean_ctor_set(v___x_3689_, 2, v___x_3687_);
lean_ctor_set(v___x_3689_, 3, v___x_3688_);
lean_inc(v_declHint_3675_);
v___x_3690_ = l_Lean_MessageData_ofConstName(v_declHint_3675_, v___x_3680_);
v_c_3691_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_3691_, 0, v___x_3689_);
lean_ctor_set(v_c_3691_, 1, v___x_3690_);
v___x_3692_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3679_, v_declHint_3675_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; 
lean_dec_ref(v_env_3679_);
lean_dec(v_declHint_3675_);
v___x_3693_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_3694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3693_);
lean_ctor_set(v___x_3694_, 1, v_c_3691_);
v___x_3695_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_3696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3694_);
lean_ctor_set(v___x_3696_, 1, v___x_3695_);
v___x_3697_ = l_Lean_MessageData_note(v___x_3696_);
v___x_3698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3698_, 0, v_msg_3674_);
lean_ctor_set(v___x_3698_, 1, v___x_3697_);
v___x_3699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3698_);
return v___x_3699_;
}
else
{
lean_object* v_val_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3735_; 
v_val_3700_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_3735_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3702_ = v___x_3692_;
v_isShared_3703_ = v_isSharedCheck_3735_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_val_3700_);
lean_dec(v___x_3692_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3735_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v_mod_3707_; uint8_t v___x_3708_; 
v___x_3704_ = lean_box(0);
v___x_3705_ = l_Lean_Environment_header(v_env_3679_);
lean_dec_ref(v_env_3679_);
v___x_3706_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3705_);
v_mod_3707_ = lean_array_get(v___x_3704_, v___x_3706_, v_val_3700_);
lean_dec(v_val_3700_);
lean_dec_ref(v___x_3706_);
v___x_3708_ = l_Lean_isPrivateName(v_declHint_3675_);
lean_dec(v_declHint_3675_);
if (v___x_3708_ == 0)
{
lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3720_; 
v___x_3709_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__5);
v___x_3710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3709_);
lean_ctor_set(v___x_3710_, 1, v_c_3691_);
v___x_3711_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_3712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3710_);
lean_ctor_set(v___x_3712_, 1, v___x_3711_);
v___x_3713_ = l_Lean_MessageData_ofName(v_mod_3707_);
v___x_3714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3712_);
lean_ctor_set(v___x_3714_, 1, v___x_3713_);
v___x_3715_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__9);
v___x_3716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3714_);
lean_ctor_set(v___x_3716_, 1, v___x_3715_);
v___x_3717_ = l_Lean_MessageData_note(v___x_3716_);
v___x_3718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3718_, 0, v_msg_3674_);
lean_ctor_set(v___x_3718_, 1, v___x_3717_);
if (v_isShared_3703_ == 0)
{
lean_ctor_set_tag(v___x_3702_, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3718_);
v___x_3720_ = v___x_3702_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v___x_3718_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
else
{
lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3733_; 
v___x_3722_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_3723_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3722_);
lean_ctor_set(v___x_3723_, 1, v_c_3691_);
v___x_3724_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__11);
v___x_3725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3723_);
lean_ctor_set(v___x_3725_, 1, v___x_3724_);
v___x_3726_ = l_Lean_MessageData_ofName(v_mod_3707_);
v___x_3727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3725_);
lean_ctor_set(v___x_3727_, 1, v___x_3726_);
v___x_3728_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___closed__13);
v___x_3729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3727_);
lean_ctor_set(v___x_3729_, 1, v___x_3728_);
v___x_3730_ = l_Lean_MessageData_note(v___x_3729_);
v___x_3731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3731_, 0, v_msg_3674_);
lean_ctor_set(v___x_3731_, 1, v___x_3730_);
if (v_isShared_3703_ == 0)
{
lean_ctor_set_tag(v___x_3702_, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3731_);
v___x_3733_ = v___x_3702_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v___x_3731_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3736_; 
lean_dec_ref(v_env_3679_);
lean_dec(v_declHint_3675_);
v___x_3736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3736_, 0, v_msg_3674_);
return v___x_3736_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_msg_3737_, lean_object* v_declHint_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_){
_start:
{
lean_object* v_res_3741_; 
v_res_3741_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_3737_, v_declHint_3738_, v___y_3739_);
lean_dec(v___y_3739_);
return v_res_3741_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6(lean_object* v_msg_3742_, lean_object* v_declHint_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_){
_start:
{
lean_object* v___x_3747_; lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3757_; 
v___x_3747_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_3742_, v_declHint_3743_, v___y_3745_);
v_a_3748_ = lean_ctor_get(v___x_3747_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3747_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3750_ = v___x_3747_;
v_isShared_3751_ = v_isSharedCheck_3757_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___x_3747_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3757_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3755_; 
v___x_3752_ = l_Lean_unknownIdentifierMessageTag;
v___x_3753_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3752_);
lean_ctor_set(v___x_3753_, 1, v_a_3748_);
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 0, v___x_3753_);
v___x_3755_ = v___x_3750_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v___x_3753_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6___boxed(lean_object* v_msg_3758_, lean_object* v_declHint_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
lean_object* v_res_3763_; 
v_res_3763_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_3758_, v_declHint_3759_, v___y_3760_, v___y_3761_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_3764_, lean_object* v_msg_3765_, lean_object* v_declHint_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_){
_start:
{
lean_object* v___x_3770_; lean_object* v_a_3771_; lean_object* v___x_3772_; 
v___x_3770_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6(v_msg_3765_, v_declHint_3766_, v___y_3767_, v___y_3768_);
v_a_3771_ = lean_ctor_get(v___x_3770_, 0);
lean_inc(v_a_3771_);
lean_dec_ref(v___x_3770_);
v___x_3772_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v_ref_3764_, v_a_3771_, v___y_3767_, v___y_3768_);
return v___x_3772_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_3773_, lean_object* v_msg_3774_, lean_object* v_declHint_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_){
_start:
{
lean_object* v_res_3779_; 
v_res_3779_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3773_, v_msg_3774_, v_declHint_3775_, v___y_3776_, v___y_3777_);
lean_dec(v___y_3777_);
lean_dec_ref(v___y_3776_);
lean_dec(v_ref_3773_);
return v_res_3779_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_3781_; lean_object* v___x_3782_; 
v___x_3781_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___closed__0));
v___x_3782_ = l_Lean_stringToMessageData(v___x_3781_);
return v___x_3782_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_3783_, lean_object* v_constName_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_){
_start:
{
lean_object* v___x_3788_; uint8_t v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; 
v___x_3788_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_3789_ = 0;
lean_inc(v_constName_3784_);
v___x_3790_ = l_Lean_MessageData_ofConstName(v_constName_3784_, v___x_3789_);
v___x_3791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3788_);
lean_ctor_set(v___x_3791_, 1, v___x_3790_);
v___x_3792_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkMatchOld_mkAlts_spec__0___closed__1);
v___x_3793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3791_);
lean_ctor_set(v___x_3793_, 1, v___x_3792_);
v___x_3794_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_3783_, v___x_3793_, v_constName_3784_, v___y_3785_, v___y_3786_);
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_3795_, lean_object* v_constName_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_){
_start:
{
lean_object* v_res_3800_; 
v_res_3800_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_3795_, v_constName_3796_, v___y_3797_, v___y_3798_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
lean_dec(v_ref_3795_);
return v_res_3800_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_){
_start:
{
lean_object* v___x_3805_; 
v___x_3805_ = l_Lean_Elab_Command_getRef___redArg(v___y_3802_);
if (lean_obj_tag(v___x_3805_) == 0)
{
lean_object* v_a_3806_; lean_object* v___x_3807_; 
v_a_3806_ = lean_ctor_get(v___x_3805_, 0);
lean_inc(v_a_3806_);
lean_dec_ref_known(v___x_3805_, 1);
v___x_3807_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_a_3806_, v_constName_3801_, v___y_3802_, v___y_3803_);
lean_dec(v_a_3806_);
return v___x_3807_;
}
else
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
lean_dec(v_constName_3801_);
v_a_3808_ = lean_ctor_get(v___x_3805_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3805_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3805_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3805_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_){
_start:
{
lean_object* v_res_3820_; 
v_res_3820_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1___redArg(v_constName_3816_, v___y_3817_, v___y_3818_);
lean_dec(v___y_3818_);
lean_dec_ref(v___y_3817_);
return v_res_3820_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0(lean_object* v_constName_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_){
_start:
{
lean_object* v___x_3825_; lean_object* v_env_3826_; uint8_t v___x_3827_; lean_object* v___x_3828_; 
v___x_3825_ = lean_st_ref_get(v___y_3823_);
v_env_3826_ = lean_ctor_get(v___x_3825_, 0);
lean_inc_ref(v_env_3826_);
lean_dec(v___x_3825_);
v___x_3827_ = 0;
lean_inc(v_constName_3821_);
v___x_3828_ = l_Lean_Environment_find_x3f(v_env_3826_, v_constName_3821_, v___x_3827_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v___x_3829_; 
v___x_3829_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1___redArg(v_constName_3821_, v___y_3822_, v___y_3823_);
return v___x_3829_;
}
else
{
lean_object* v_val_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3837_; 
lean_dec(v_constName_3821_);
v_val_3830_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3837_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3837_ == 0)
{
v___x_3832_ = v___x_3828_;
v_isShared_3833_ = v_isSharedCheck_3837_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_val_3830_);
lean_dec(v___x_3828_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3837_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v___x_3835_; 
if (v_isShared_3833_ == 0)
{
lean_ctor_set_tag(v___x_3832_, 0);
v___x_3835_ = v___x_3832_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v_val_3830_);
v___x_3835_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
return v___x_3835_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0___boxed(lean_object* v_constName_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_){
_start:
{
lean_object* v_res_3842_; 
v_res_3842_ = l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0(v_constName_3838_, v___y_3839_, v___y_3840_);
lean_dec(v___y_3840_);
lean_dec_ref(v___y_3839_);
return v_res_3842_;
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__1(uint8_t v___x_3843_, lean_object* v_x_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_){
_start:
{
if (lean_obj_tag(v_x_3844_) == 0)
{
uint8_t v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; 
v___x_3848_ = 1;
v___x_3849_ = lean_box(v___x_3848_);
v___x_3850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3850_, 0, v___x_3849_);
return v___x_3850_;
}
else
{
lean_object* v_head_3851_; lean_object* v_tail_3852_; lean_object* v___x_3853_; 
v_head_3851_ = lean_ctor_get(v_x_3844_, 0);
lean_inc(v_head_3851_);
v_tail_3852_ = lean_ctor_get(v_x_3844_, 1);
lean_inc(v_tail_3852_);
lean_dec_ref_known(v_x_3844_, 2);
v___x_3853_ = l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0(v_head_3851_, v___y_3845_, v___y_3846_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v_a_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3874_; 
v_a_3854_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3856_ = v___x_3853_;
v_isShared_3857_ = v_isSharedCheck_3874_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_a_3854_);
lean_dec(v___x_3853_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3874_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v___y_3859_; uint8_t v_a_3860_; 
if (lean_obj_tag(v_a_3854_) == 6)
{
lean_object* v_val_3862_; lean_object* v_numFields_3863_; lean_object* v___x_3864_; uint8_t v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3868_; 
v_val_3862_ = lean_ctor_get(v_a_3854_, 0);
lean_inc_ref(v_val_3862_);
lean_dec_ref_known(v_a_3854_, 1);
v_numFields_3863_ = lean_ctor_get(v_val_3862_, 4);
lean_inc(v_numFields_3863_);
lean_dec_ref(v_val_3862_);
v___x_3864_ = lean_unsigned_to_nat(0u);
v___x_3865_ = lean_nat_dec_eq(v_numFields_3863_, v___x_3864_);
lean_dec(v_numFields_3863_);
v___x_3866_ = lean_box(v___x_3865_);
if (v_isShared_3857_ == 0)
{
lean_ctor_set(v___x_3856_, 0, v___x_3866_);
v___x_3868_ = v___x_3856_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v___x_3866_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
v___y_3859_ = v___x_3868_;
v_a_3860_ = v___x_3865_;
goto v___jp_3858_;
}
}
else
{
lean_object* v___x_3870_; lean_object* v___x_3872_; 
lean_dec(v_a_3854_);
v___x_3870_ = lean_box(v___x_3843_);
if (v_isShared_3857_ == 0)
{
lean_ctor_set(v___x_3856_, 0, v___x_3870_);
v___x_3872_ = v___x_3856_;
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
v___y_3859_ = v___x_3872_;
v_a_3860_ = v___x_3843_;
goto v___jp_3858_;
}
}
v___jp_3858_:
{
if (v_a_3860_ == 0)
{
lean_dec(v_tail_3852_);
return v___y_3859_;
}
else
{
lean_dec_ref(v___y_3859_);
v_x_3844_ = v_tail_3852_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3882_; 
lean_dec(v_tail_3852_);
v_a_3875_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_3882_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3882_ == 0)
{
v___x_3877_ = v___x_3853_;
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_a_3875_);
lean_dec(v___x_3853_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3882_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v___x_3880_; 
if (v_isShared_3878_ == 0)
{
v___x_3880_ = v___x_3877_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_a_3875_);
v___x_3880_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
return v___x_3880_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__1___boxed(lean_object* v___x_3883_, lean_object* v_x_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_){
_start:
{
uint8_t v___x_4422__boxed_3888_; lean_object* v_res_3889_; 
v___x_4422__boxed_3888_ = lean_unbox(v___x_3883_);
v_res_3889_ = l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__1(v___x_4422__boxed_3888_, v_x_3884_, v___y_3885_, v___y_3886_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
return v_res_3889_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0(lean_object* v_declName_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_){
_start:
{
lean_object* v___x_3894_; 
v___x_3894_ = l_Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0(v_declName_3890_, v___y_3891_, v___y_3892_);
if (lean_obj_tag(v___x_3894_) == 0)
{
lean_object* v_a_3895_; lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_3950_; 
v_a_3895_ = lean_ctor_get(v___x_3894_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3894_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3897_ = v___x_3894_;
v_isShared_3898_ = v_isSharedCheck_3950_;
goto v_resetjp_3896_;
}
else
{
lean_inc(v_a_3895_);
lean_dec(v___x_3894_);
v___x_3897_ = lean_box(0);
v_isShared_3898_ = v_isSharedCheck_3950_;
goto v_resetjp_3896_;
}
v_resetjp_3896_:
{
if (lean_obj_tag(v_a_3895_) == 5)
{
lean_object* v_val_3899_; lean_object* v_toConstantVal_3900_; lean_object* v_numParams_3901_; lean_object* v_numIndices_3902_; lean_object* v_ctors_3903_; uint8_t v_isRec_3904_; uint8_t v_isUnsafe_3905_; lean_object* v_type_3906_; uint8_t v___x_3907_; 
v_val_3899_ = lean_ctor_get(v_a_3895_, 0);
lean_inc_ref(v_val_3899_);
lean_dec_ref_known(v_a_3895_, 1);
v_toConstantVal_3900_ = lean_ctor_get(v_val_3899_, 0);
v_numParams_3901_ = lean_ctor_get(v_val_3899_, 1);
lean_inc(v_numParams_3901_);
v_numIndices_3902_ = lean_ctor_get(v_val_3899_, 2);
lean_inc(v_numIndices_3902_);
v_ctors_3903_ = lean_ctor_get(v_val_3899_, 4);
lean_inc(v_ctors_3903_);
v_isRec_3904_ = lean_ctor_get_uint8(v_val_3899_, sizeof(void*)*6);
v_isUnsafe_3905_ = lean_ctor_get_uint8(v_val_3899_, sizeof(void*)*6 + 1);
v_type_3906_ = lean_ctor_get(v_toConstantVal_3900_, 2);
v___x_3907_ = l_Lean_Expr_isProp(v_type_3906_);
if (v___x_3907_ == 0)
{
lean_object* v___x_3908_; lean_object* v___x_3909_; uint8_t v___x_3910_; 
v___x_3908_ = l_Lean_InductiveVal_numTypeFormers(v_val_3899_);
lean_dec_ref(v_val_3899_);
v___x_3909_ = lean_unsigned_to_nat(1u);
v___x_3910_ = lean_nat_dec_eq(v___x_3908_, v___x_3909_);
lean_dec(v___x_3908_);
if (v___x_3910_ == 0)
{
lean_object* v___x_3911_; lean_object* v___x_3913_; 
lean_dec(v_ctors_3903_);
lean_dec(v_numIndices_3902_);
lean_dec(v_numParams_3901_);
v___x_3911_ = lean_box(v___x_3910_);
if (v_isShared_3898_ == 0)
{
lean_ctor_set(v___x_3897_, 0, v___x_3911_);
v___x_3913_ = v___x_3897_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v___x_3911_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
else
{
lean_object* v___x_3915_; uint8_t v___x_3916_; 
v___x_3915_ = lean_unsigned_to_nat(0u);
v___x_3916_ = lean_nat_dec_eq(v_numIndices_3902_, v___x_3915_);
lean_dec(v_numIndices_3902_);
if (v___x_3916_ == 0)
{
lean_object* v___x_3917_; lean_object* v___x_3919_; 
lean_dec(v_ctors_3903_);
lean_dec(v_numParams_3901_);
v___x_3917_ = lean_box(v___x_3916_);
if (v_isShared_3898_ == 0)
{
lean_ctor_set(v___x_3897_, 0, v___x_3917_);
v___x_3919_ = v___x_3897_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v___x_3917_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
else
{
uint8_t v___x_3921_; 
v___x_3921_ = lean_nat_dec_eq(v_numParams_3901_, v___x_3915_);
lean_dec(v_numParams_3901_);
if (v___x_3921_ == 0)
{
lean_object* v___x_3922_; lean_object* v___x_3924_; 
lean_dec(v_ctors_3903_);
v___x_3922_ = lean_box(v___x_3921_);
if (v_isShared_3898_ == 0)
{
lean_ctor_set(v___x_3897_, 0, v___x_3922_);
v___x_3924_ = v___x_3897_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v___x_3922_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
else
{
uint8_t v___x_3926_; 
v___x_3926_ = l_List_isEmpty___redArg(v_ctors_3903_);
if (v___x_3926_ == 0)
{
if (v_isRec_3904_ == 0)
{
if (v_isUnsafe_3905_ == 0)
{
lean_object* v___x_3927_; 
lean_del_object(v___x_3897_);
v___x_3927_ = l_List_allM___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__1(v_isUnsafe_3905_, v_ctors_3903_, v___y_3891_, v___y_3892_);
return v___x_3927_;
}
else
{
lean_object* v___x_3928_; lean_object* v___x_3930_; 
lean_dec(v_ctors_3903_);
v___x_3928_ = lean_box(v_isRec_3904_);
if (v_isShared_3898_ == 0)
{
lean_ctor_set(v___x_3897_, 0, v___x_3928_);
v___x_3930_ = v___x_3897_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v___x_3928_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
else
{
lean_object* v___x_3932_; lean_object* v___x_3934_; 
lean_dec(v_ctors_3903_);
v___x_3932_ = lean_box(v___x_3926_);
if (v_isShared_3898_ == 0)
{
lean_ctor_set(v___x_3897_, 0, v___x_3932_);
v___x_3934_ = v___x_3897_;
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
lean_dec(v_ctors_3903_);
v___x_3936_ = lean_box(v___x_3907_);
if (v_isShared_3898_ == 0)
{
lean_ctor_set(v___x_3897_, 0, v___x_3936_);
v___x_3938_ = v___x_3897_;
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
}
}
}
else
{
uint8_t v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3943_; 
lean_dec(v_ctors_3903_);
lean_dec(v_numIndices_3902_);
lean_dec(v_numParams_3901_);
lean_dec_ref(v_val_3899_);
v___x_3940_ = 0;
v___x_3941_ = lean_box(v___x_3940_);
if (v_isShared_3898_ == 0)
{
lean_ctor_set(v___x_3897_, 0, v___x_3941_);
v___x_3943_ = v___x_3897_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v___x_3941_);
v___x_3943_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
return v___x_3943_;
}
}
}
else
{
uint8_t v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3948_; 
lean_dec(v_a_3895_);
v___x_3945_ = 0;
v___x_3946_ = lean_box(v___x_3945_);
if (v_isShared_3898_ == 0)
{
lean_ctor_set(v___x_3897_, 0, v___x_3946_);
v___x_3948_ = v___x_3897_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v___x_3946_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
}
}
}
}
else
{
lean_object* v_a_3951_; lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_3958_; 
v_a_3951_ = lean_ctor_get(v___x_3894_, 0);
v_isSharedCheck_3958_ = !lean_is_exclusive(v___x_3894_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3953_ = v___x_3894_;
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
else
{
lean_inc(v_a_3951_);
lean_dec(v___x_3894_);
v___x_3953_ = lean_box(0);
v_isShared_3954_ = v_isSharedCheck_3958_;
goto v_resetjp_3952_;
}
v_resetjp_3952_:
{
lean_object* v___x_3956_; 
if (v_isShared_3954_ == 0)
{
v___x_3956_ = v___x_3953_;
goto v_reusejp_3955_;
}
else
{
lean_object* v_reuseFailAlloc_3957_; 
v_reuseFailAlloc_3957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_a_3951_);
v___x_3956_ = v_reuseFailAlloc_3957_;
goto v_reusejp_3955_;
}
v_reusejp_3955_:
{
return v___x_3956_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0___boxed(lean_object* v_declName_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_){
_start:
{
lean_object* v_res_3963_; 
v_res_3963_ = l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0(v_declName_3959_, v___y_3960_, v___y_3961_);
lean_dec(v___y_3961_);
lean_dec_ref(v___y_3960_);
return v_res_3963_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__1(lean_object* v_as_3964_, size_t v_i_3965_, size_t v_stop_3966_, lean_object* v_b_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_){
_start:
{
uint8_t v___x_3971_; 
v___x_3971_ = lean_usize_dec_eq(v_i_3965_, v_stop_3966_);
if (v___x_3971_ == 0)
{
lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3972_ = lean_array_uget_borrowed(v_as_3964_, v_i_3965_);
lean_inc(v___x_3972_);
v___x_3973_ = l_Lean_Elab_Command_elabCommand(v___x_3972_, v___y_3968_, v___y_3969_);
if (lean_obj_tag(v___x_3973_) == 0)
{
lean_object* v_a_3974_; size_t v___x_3975_; size_t v___x_3976_; 
v_a_3974_ = lean_ctor_get(v___x_3973_, 0);
lean_inc(v_a_3974_);
lean_dec_ref_known(v___x_3973_, 1);
v___x_3975_ = ((size_t)1ULL);
v___x_3976_ = lean_usize_add(v_i_3965_, v___x_3975_);
v_i_3965_ = v___x_3976_;
v_b_3967_ = v_a_3974_;
goto _start;
}
else
{
return v___x_3973_;
}
}
else
{
lean_object* v___x_3978_; 
v___x_3978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3978_, 0, v_b_3967_);
return v___x_3978_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__1___boxed(lean_object* v_as_3979_, lean_object* v_i_3980_, lean_object* v_stop_3981_, lean_object* v_b_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_){
_start:
{
size_t v_i_boxed_3986_; size_t v_stop_boxed_3987_; lean_object* v_res_3988_; 
v_i_boxed_3986_ = lean_unbox_usize(v_i_3980_);
lean_dec(v_i_3980_);
v_stop_boxed_3987_ = lean_unbox_usize(v_stop_3981_);
lean_dec(v_stop_3981_);
v_res_3988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__1(v_as_3979_, v_i_boxed_3986_, v_stop_boxed_3987_, v_b_3982_, v___y_3983_, v___y_3984_);
lean_dec(v___y_3984_);
lean_dec_ref(v___y_3983_);
lean_dec_ref(v_as_3979_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__1(lean_object* v_declName_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_){
_start:
{
lean_object* v___x_3993_; 
lean_inc(v_declName_3989_);
v___x_3993_ = l_Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0(v_declName_3989_, v___y_3990_, v___y_3991_);
if (lean_obj_tag(v___x_3993_) == 0)
{
lean_object* v_a_3994_; lean_object* v___y_3995_; lean_object* v___x_3996_; 
v_a_3994_ = lean_ctor_get(v___x_3993_, 0);
lean_inc(v_a_3994_);
lean_dec_ref_known(v___x_3993_, 1);
v___y_3995_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__0___boxed), 9, 2);
lean_closure_set(v___y_3995_, 0, v_a_3994_);
lean_closure_set(v___y_3995_, 1, v_declName_3989_);
v___x_3996_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___y_3995_, v___y_3990_, v___y_3991_);
if (lean_obj_tag(v___x_3996_) == 0)
{
lean_object* v_a_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4018_; 
v_a_3997_ = lean_ctor_get(v___x_3996_, 0);
v_isSharedCheck_4018_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4018_ == 0)
{
v___x_3999_ = v___x_3996_;
v_isShared_4000_ = v_isSharedCheck_4018_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_a_3997_);
lean_dec(v___x_3996_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4018_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; uint8_t v___x_4004_; 
v___x_4001_ = lean_unsigned_to_nat(0u);
v___x_4002_ = lean_array_get_size(v_a_3997_);
v___x_4003_ = lean_box(0);
v___x_4004_ = lean_nat_dec_lt(v___x_4001_, v___x_4002_);
if (v___x_4004_ == 0)
{
lean_object* v___x_4006_; 
lean_dec(v_a_3997_);
if (v_isShared_4000_ == 0)
{
lean_ctor_set(v___x_3999_, 0, v___x_4003_);
v___x_4006_ = v___x_3999_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v___x_4003_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
}
}
else
{
uint8_t v___x_4008_; 
v___x_4008_ = lean_nat_dec_le(v___x_4002_, v___x_4002_);
if (v___x_4008_ == 0)
{
if (v___x_4004_ == 0)
{
lean_object* v___x_4010_; 
lean_dec(v_a_3997_);
if (v_isShared_4000_ == 0)
{
lean_ctor_set(v___x_3999_, 0, v___x_4003_);
v___x_4010_ = v___x_3999_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v___x_4003_);
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
size_t v___x_4012_; size_t v___x_4013_; lean_object* v___x_4014_; 
lean_del_object(v___x_3999_);
v___x_4012_ = ((size_t)0ULL);
v___x_4013_ = lean_usize_of_nat(v___x_4002_);
v___x_4014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__1(v_a_3997_, v___x_4012_, v___x_4013_, v___x_4003_, v___y_3990_, v___y_3991_);
lean_dec(v_a_3997_);
return v___x_4014_;
}
}
else
{
size_t v___x_4015_; size_t v___x_4016_; lean_object* v___x_4017_; 
lean_del_object(v___x_3999_);
v___x_4015_ = ((size_t)0ULL);
v___x_4016_ = lean_usize_of_nat(v___x_4002_);
v___x_4017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__1(v_a_3997_, v___x_4015_, v___x_4016_, v___x_4003_, v___y_3990_, v___y_3991_);
lean_dec(v_a_3997_);
return v___x_4017_;
}
}
}
}
else
{
lean_object* v_a_4019_; lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4026_; 
v_a_4019_ = lean_ctor_get(v___x_3996_, 0);
v_isSharedCheck_4026_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4026_ == 0)
{
v___x_4021_ = v___x_3996_;
v_isShared_4022_ = v_isSharedCheck_4026_;
goto v_resetjp_4020_;
}
else
{
lean_inc(v_a_4019_);
lean_dec(v___x_3996_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4026_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v___x_4024_; 
if (v_isShared_4022_ == 0)
{
v___x_4024_ = v___x_4021_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v_a_4019_);
v___x_4024_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
return v___x_4024_;
}
}
}
}
else
{
lean_object* v_a_4027_; lean_object* v___x_4029_; uint8_t v_isShared_4030_; uint8_t v_isSharedCheck_4034_; 
lean_dec(v_declName_3989_);
v_a_4027_ = lean_ctor_get(v___x_3993_, 0);
v_isSharedCheck_4034_ = !lean_is_exclusive(v___x_3993_);
if (v_isSharedCheck_4034_ == 0)
{
v___x_4029_ = v___x_3993_;
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
else
{
lean_inc(v_a_4027_);
lean_dec(v___x_3993_);
v___x_4029_ = lean_box(0);
v_isShared_4030_ = v_isSharedCheck_4034_;
goto v_resetjp_4028_;
}
v_resetjp_4028_:
{
lean_object* v___x_4032_; 
if (v_isShared_4030_ == 0)
{
v___x_4032_ = v___x_4029_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v_a_4027_);
v___x_4032_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
return v___x_4032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__1___boxed(lean_object* v_declName_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_){
_start:
{
lean_object* v_res_4039_; 
v_res_4039_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__1(v_declName_4035_, v___y_4036_, v___y_4037_);
lean_dec(v___y_4037_);
lean_dec_ref(v___y_4036_);
return v_res_4039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance(lean_object* v_declName_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_){
_start:
{
lean_object* v___f_4044_; lean_object* v___x_4045_; 
lean_inc(v_declName_4040_);
v___f_4044_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___lam__1___boxed), 4, 1);
lean_closure_set(v___f_4044_, 0, v_declName_4040_);
v___x_4045_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(v_declName_4040_, v___f_4044_, v_a_4041_, v_a_4042_);
return v___x_4045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance___boxed(lean_object* v_declName_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_){
_start:
{
lean_object* v_res_4050_; 
v_res_4050_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance(v_declName_4046_, v_a_4047_, v_a_4048_);
lean_dec(v_a_4048_);
lean_dec_ref(v_a_4047_);
return v_res_4050_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_4051_, lean_object* v_constName_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_){
_start:
{
lean_object* v___x_4056_; 
v___x_4056_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1___redArg(v_constName_4052_, v___y_4053_, v___y_4054_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_4057_, lean_object* v_constName_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_){
_start:
{
lean_object* v_res_4062_; 
v_res_4062_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1(v_00_u03b1_4057_, v_constName_4058_, v___y_4059_, v___y_4060_);
lean_dec(v___y_4060_);
lean_dec_ref(v___y_4059_);
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_4063_, lean_object* v_ref_4064_, lean_object* v_constName_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_){
_start:
{
lean_object* v___x_4069_; 
v___x_4069_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_4064_, v_constName_4065_, v___y_4066_, v___y_4067_);
return v___x_4069_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4070_, lean_object* v_ref_4071_, lean_object* v_constName_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_){
_start:
{
lean_object* v_res_4076_; 
v_res_4076_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_4070_, v_ref_4071_, v_constName_4072_, v___y_4073_, v___y_4074_);
lean_dec(v___y_4074_);
lean_dec_ref(v___y_4073_);
lean_dec(v_ref_4071_);
return v_res_4076_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_4077_, lean_object* v_ref_4078_, lean_object* v_msg_4079_, lean_object* v_declHint_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_){
_start:
{
lean_object* v___x_4084_; 
v___x_4084_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_4078_, v_msg_4079_, v_declHint_4080_, v___y_4081_, v___y_4082_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_4085_, lean_object* v_ref_4086_, lean_object* v_msg_4087_, lean_object* v_declHint_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_){
_start:
{
lean_object* v_res_4092_; 
v_res_4092_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_4085_, v_ref_4086_, v_msg_4087_, v_declHint_4088_, v___y_4089_, v___y_4090_);
lean_dec(v___y_4090_);
lean_dec_ref(v___y_4089_);
lean_dec(v_ref_4086_);
return v_res_4092_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7(lean_object* v_msg_4093_, lean_object* v_declHint_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_){
_start:
{
lean_object* v___x_4098_; 
v___x_4098_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_4093_, v_declHint_4094_, v___y_4096_);
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7___boxed(lean_object* v_msg_4099_, lean_object* v_declHint_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_){
_start:
{
lean_object* v_res_4104_; 
v_res_4104_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__6_spec__7(v_msg_4099_, v_declHint_4100_, v___y_4101_, v___y_4102_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
return v_res_4104_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_4105_, lean_object* v_ref_4106_, lean_object* v_msg_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
lean_object* v___x_4111_; 
v___x_4111_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___redArg(v_ref_4106_, v_msg_4107_, v___y_4108_, v___y_4109_);
return v___x_4111_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_4112_, lean_object* v_ref_4113_, lean_object* v_msg_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_){
_start:
{
lean_object* v_res_4118_; 
v_res_4118_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7(v_00_u03b1_4112_, v_ref_4113_, v_msg_4114_, v___y_4115_, v___y_4116_);
lean_dec(v___y_4116_);
lean_dec_ref(v___y_4115_);
lean_dec(v_ref_4113_);
return v_res_4118_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10(lean_object* v_msgData_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_){
_start:
{
lean_object* v___x_4123_; 
v___x_4123_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___redArg(v_msgData_4119_, v___y_4121_);
return v___x_4123_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10___boxed(lean_object* v_msgData_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_){
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__10(v_msgData_4124_, v___y_4125_, v___y_4126_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_4129_, lean_object* v_msg_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_){
_start:
{
lean_object* v___x_4134_; 
v___x_4134_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_4130_, v___y_4131_, v___y_4132_);
return v___x_4134_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4135_, lean_object* v_msg_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_){
_start:
{
lean_object* v_res_4140_; 
v_res_4140_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9(v_00_u03b1_4135_, v_msg_4136_, v___y_4137_, v___y_4138_);
lean_dec(v___y_4138_);
lean_dec_ref(v___y_4137_);
return v_res_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11(lean_object* v_msgData_4141_, lean_object* v_macroStack_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_){
_start:
{
lean_object* v___x_4146_; 
v___x_4146_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11___redArg(v_msgData_4141_, v_macroStack_4142_, v___y_4144_);
return v___x_4146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11___boxed(lean_object* v_msgData_4147_, lean_object* v_macroStack_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_){
_start:
{
lean_object* v_res_4152_; 
v_res_4152_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_isEnumType___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance_spec__0_spec__0_spec__1_spec__3_spec__5_spec__7_spec__9_spec__11(v_msgData_4147_, v_macroStack_4148_, v___y_4149_, v___y_4150_);
lean_dec(v___y_4150_);
lean_dec_ref(v___y_4149_);
return v_res_4152_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1___redArg(lean_object* v_declName_4153_, lean_object* v___y_4154_){
_start:
{
lean_object* v___x_4156_; lean_object* v_env_4157_; uint8_t v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; 
v___x_4156_ = lean_st_ref_get(v___y_4154_);
v_env_4157_ = lean_ctor_get(v___x_4156_, 0);
lean_inc_ref(v_env_4157_);
lean_dec(v___x_4156_);
v___x_4158_ = l_Lean_isInductiveCore(v_env_4157_, v_declName_4153_);
v___x_4159_ = lean_box(v___x_4158_);
v___x_4160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4160_, 0, v___x_4159_);
return v___x_4160_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1___redArg___boxed(lean_object* v_declName_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_){
_start:
{
lean_object* v_res_4164_; 
v_res_4164_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1___redArg(v_declName_4161_, v___y_4162_);
lean_dec(v___y_4162_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1(lean_object* v_declName_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_){
_start:
{
lean_object* v___x_4169_; 
v___x_4169_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1___redArg(v_declName_4165_, v___y_4167_);
return v___x_4169_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1___boxed(lean_object* v_declName_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_){
_start:
{
lean_object* v_res_4174_; 
v_res_4174_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1(v_declName_4170_, v___y_4171_, v___y_4172_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___lam__0(uint8_t v_____do__lift_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_){
_start:
{
if (v_____do__lift_4175_ == 0)
{
uint8_t v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; 
v___x_4179_ = 1;
v___x_4180_ = lean_box(v___x_4179_);
v___x_4181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4181_, 0, v___x_4180_);
return v___x_4181_;
}
else
{
uint8_t v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; 
v___x_4182_ = 0;
v___x_4183_ = lean_box(v___x_4182_);
v___x_4184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4184_, 0, v___x_4183_);
return v___x_4184_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___lam__0___boxed(lean_object* v_____do__lift_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_){
_start:
{
uint8_t v_____do__lift_1654__boxed_4189_; lean_object* v_res_4190_; 
v_____do__lift_1654__boxed_4189_ = lean_unbox(v_____do__lift_4185_);
v_res_4190_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___lam__0(v_____do__lift_1654__boxed_4189_, v___y_4186_, v___y_4187_);
lean_dec(v___y_4187_);
lean_dec_ref(v___y_4186_);
return v_res_4190_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__2(lean_object* v_as_4191_, size_t v_i_4192_, size_t v_stop_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_){
_start:
{
uint8_t v___x_4201_; 
v___x_4201_ = lean_usize_dec_eq(v_i_4192_, v_stop_4193_);
if (v___x_4201_ == 0)
{
uint8_t v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; 
v___x_4202_ = 1;
v___x_4203_ = lean_array_uget_borrowed(v_as_4191_, v_i_4192_);
lean_inc(v___x_4203_);
v___x_4204_ = l_Lean_isInductive___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__1___redArg(v___x_4203_, v___y_4195_);
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_object* v_a_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4214_; 
v_a_4205_ = lean_ctor_get(v___x_4204_, 0);
v_isSharedCheck_4214_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4207_ = v___x_4204_;
v_isShared_4208_ = v_isSharedCheck_4214_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_a_4205_);
lean_dec(v___x_4204_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4214_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
uint8_t v___x_4209_; 
v___x_4209_ = lean_unbox(v_a_4205_);
lean_dec(v_a_4205_);
if (v___x_4209_ == 0)
{
lean_object* v___x_4210_; lean_object* v___x_4212_; 
v___x_4210_ = lean_box(v___x_4202_);
if (v_isShared_4208_ == 0)
{
lean_ctor_set(v___x_4207_, 0, v___x_4210_);
v___x_4212_ = v___x_4207_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v___x_4210_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
return v___x_4212_;
}
}
else
{
lean_del_object(v___x_4207_);
goto v___jp_4197_;
}
}
}
else
{
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_object* v_a_4215_; lean_object* v___x_4217_; uint8_t v_isShared_4218_; uint8_t v_isSharedCheck_4224_; 
v_a_4215_ = lean_ctor_get(v___x_4204_, 0);
v_isSharedCheck_4224_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4224_ == 0)
{
v___x_4217_ = v___x_4204_;
v_isShared_4218_ = v_isSharedCheck_4224_;
goto v_resetjp_4216_;
}
else
{
lean_inc(v_a_4215_);
lean_dec(v___x_4204_);
v___x_4217_ = lean_box(0);
v_isShared_4218_ = v_isSharedCheck_4224_;
goto v_resetjp_4216_;
}
v_resetjp_4216_:
{
uint8_t v___x_4219_; 
v___x_4219_ = lean_unbox(v_a_4215_);
lean_dec(v_a_4215_);
if (v___x_4219_ == 0)
{
lean_del_object(v___x_4217_);
goto v___jp_4197_;
}
else
{
lean_object* v___x_4220_; lean_object* v___x_4222_; 
v___x_4220_ = lean_box(v___x_4202_);
if (v_isShared_4218_ == 0)
{
lean_ctor_set_tag(v___x_4217_, 0);
lean_ctor_set(v___x_4217_, 0, v___x_4220_);
v___x_4222_ = v___x_4217_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v___x_4220_);
v___x_4222_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
return v___x_4222_;
}
}
}
}
else
{
return v___x_4204_;
}
}
}
else
{
uint8_t v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4225_ = 0;
v___x_4226_ = lean_box(v___x_4225_);
v___x_4227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4227_, 0, v___x_4226_);
return v___x_4227_;
}
v___jp_4197_:
{
size_t v___x_4198_; size_t v___x_4199_; 
v___x_4198_ = ((size_t)1ULL);
v___x_4199_ = lean_usize_add(v_i_4192_, v___x_4198_);
v_i_4192_ = v___x_4199_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__2___boxed(lean_object* v_as_4228_, lean_object* v_i_4229_, lean_object* v_stop_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_){
_start:
{
size_t v_i_boxed_4234_; size_t v_stop_boxed_4235_; lean_object* v_res_4236_; 
v_i_boxed_4234_ = lean_unbox_usize(v_i_4229_);
lean_dec(v_i_4229_);
v_stop_boxed_4235_ = lean_unbox_usize(v_stop_4230_);
lean_dec(v_stop_4230_);
v_res_4236_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__2(v_as_4228_, v_i_boxed_4234_, v_stop_boxed_4235_, v___y_4231_, v___y_4232_);
lean_dec(v___y_4232_);
lean_dec_ref(v___y_4231_);
lean_dec_ref(v_as_4228_);
return v_res_4236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__0(lean_object* v_as_4237_, size_t v_sz_4238_, size_t v_i_4239_, lean_object* v_b_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_){
_start:
{
uint8_t v___x_4244_; 
v___x_4244_ = lean_usize_dec_lt(v_i_4239_, v_sz_4238_);
if (v___x_4244_ == 0)
{
lean_object* v___x_4245_; 
v___x_4245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4245_, 0, v_b_4240_);
return v___x_4245_;
}
else
{
lean_object* v_a_4246_; lean_object* v___x_4247_; 
v_a_4246_ = lean_array_uget_borrowed(v_as_4237_, v_i_4239_);
lean_inc(v_a_4246_);
v___x_4247_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstance(v_a_4246_, v___y_4241_, v___y_4242_);
if (lean_obj_tag(v___x_4247_) == 0)
{
lean_object* v___x_4248_; size_t v___x_4249_; size_t v___x_4250_; 
lean_dec_ref_known(v___x_4247_, 1);
v___x_4248_ = lean_box(0);
v___x_4249_ = ((size_t)1ULL);
v___x_4250_ = lean_usize_add(v_i_4239_, v___x_4249_);
v_i_4239_ = v___x_4250_;
v_b_4240_ = v___x_4248_;
goto _start;
}
else
{
return v___x_4247_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__0___boxed(lean_object* v_as_4252_, lean_object* v_sz_4253_, lean_object* v_i_4254_, lean_object* v_b_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_){
_start:
{
size_t v_sz_boxed_4259_; size_t v_i_boxed_4260_; lean_object* v_res_4261_; 
v_sz_boxed_4259_ = lean_unbox_usize(v_sz_4253_);
lean_dec(v_sz_4253_);
v_i_boxed_4260_ = lean_unbox_usize(v_i_4254_);
lean_dec(v_i_4254_);
v_res_4261_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__0(v_as_4252_, v_sz_boxed_4259_, v_i_boxed_4260_, v_b_4255_, v___y_4256_, v___y_4257_);
lean_dec(v___y_4257_);
lean_dec_ref(v___y_4256_);
lean_dec_ref(v_as_4252_);
return v_res_4261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler(lean_object* v_declNames_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_){
_start:
{
lean_object* v___y_4290_; lean_object* v___x_4293_; lean_object* v___x_4294_; uint8_t v___x_4295_; 
v___x_4293_ = lean_unsigned_to_nat(0u);
v___x_4294_ = lean_array_get_size(v_declNames_4262_);
v___x_4295_ = lean_nat_dec_lt(v___x_4293_, v___x_4294_);
if (v___x_4295_ == 0)
{
lean_object* v___x_4296_; 
v___x_4296_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___lam__0(v___x_4295_, v_a_4263_, v_a_4264_);
v___y_4290_ = v___x_4296_;
goto v___jp_4289_;
}
else
{
if (v___x_4295_ == 0)
{
goto v___jp_4266_;
}
else
{
size_t v___x_4297_; size_t v___x_4298_; lean_object* v___x_4299_; 
v___x_4297_ = ((size_t)0ULL);
v___x_4298_ = lean_usize_of_nat(v___x_4294_);
v___x_4299_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__2(v_declNames_4262_, v___x_4297_, v___x_4298_, v_a_4263_, v_a_4264_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_object* v_a_4300_; uint8_t v___x_4301_; lean_object* v___x_4302_; 
v_a_4300_ = lean_ctor_get(v___x_4299_, 0);
lean_inc(v_a_4300_);
lean_dec_ref_known(v___x_4299_, 1);
v___x_4301_ = lean_unbox(v_a_4300_);
lean_dec(v_a_4300_);
v___x_4302_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___lam__0(v___x_4301_, v_a_4263_, v_a_4264_);
v___y_4290_ = v___x_4302_;
goto v___jp_4289_;
}
else
{
v___y_4290_ = v___x_4299_;
goto v___jp_4289_;
}
}
}
v___jp_4266_:
{
lean_object* v___x_4267_; size_t v_sz_4268_; size_t v___x_4269_; lean_object* v___x_4270_; 
v___x_4267_ = lean_box(0);
v_sz_4268_ = lean_array_size(v_declNames_4262_);
v___x_4269_ = ((size_t)0ULL);
v___x_4270_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler_spec__0(v_declNames_4262_, v_sz_4268_, v___x_4269_, v___x_4267_, v_a_4263_, v_a_4264_);
if (lean_obj_tag(v___x_4270_) == 0)
{
lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4279_; 
v_isSharedCheck_4279_ = !lean_is_exclusive(v___x_4270_);
if (v_isSharedCheck_4279_ == 0)
{
lean_object* v_unused_4280_; 
v_unused_4280_ = lean_ctor_get(v___x_4270_, 0);
lean_dec(v_unused_4280_);
v___x_4272_ = v___x_4270_;
v_isShared_4273_ = v_isSharedCheck_4279_;
goto v_resetjp_4271_;
}
else
{
lean_dec(v___x_4270_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4279_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
uint8_t v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4277_; 
v___x_4274_ = 1;
v___x_4275_ = lean_box(v___x_4274_);
if (v_isShared_4273_ == 0)
{
lean_ctor_set(v___x_4272_, 0, v___x_4275_);
v___x_4277_ = v___x_4272_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v___x_4275_);
v___x_4277_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
return v___x_4277_;
}
}
}
else
{
lean_object* v_a_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4288_; 
v_a_4281_ = lean_ctor_get(v___x_4270_, 0);
v_isSharedCheck_4288_ = !lean_is_exclusive(v___x_4270_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4283_ = v___x_4270_;
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_a_4281_);
lean_dec(v___x_4270_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4286_; 
if (v_isShared_4284_ == 0)
{
v___x_4286_ = v___x_4283_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_a_4281_);
v___x_4286_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
return v___x_4286_;
}
}
}
}
v___jp_4289_:
{
if (lean_obj_tag(v___y_4290_) == 0)
{
lean_object* v_a_4291_; uint8_t v___x_4292_; 
v_a_4291_ = lean_ctor_get(v___y_4290_, 0);
v___x_4292_ = lean_unbox(v_a_4291_);
if (v___x_4292_ == 0)
{
return v___y_4290_;
}
else
{
lean_dec_ref_known(v___y_4290_, 1);
goto v___jp_4266_;
}
}
else
{
return v___y_4290_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler___boxed(lean_object* v_declNames_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_){
_start:
{
lean_object* v_res_4307_; 
v_res_4307_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceHandler(v_declNames_4303_, v_a_4304_, v_a_4305_);
lean_dec(v_a_4305_);
lean_dec_ref(v_a_4304_);
lean_dec_ref(v_declNames_4303_);
return v_res_4307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; 
v___x_4356_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdHeader___closed__0));
v___x_4357_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__0_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_));
v___x_4358_ = l_Lean_Elab_registerDerivingHandler(v___x_4356_, v___x_4357_);
if (lean_obj_tag(v___x_4358_) == 0)
{
lean_object* v___x_4359_; uint8_t v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; 
lean_dec_ref_known(v___x_4358_, 1);
v___x_4359_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_mkOrdInstanceCmds___closed__0));
v___x_4360_ = 0;
v___x_4361_ = ((lean_object*)(l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn___closed__18_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_));
v___x_4362_ = l_Lean_registerTraceClass(v___x_4359_, v___x_4360_, v___x_4361_);
return v___x_4362_;
}
else
{
return v___x_4358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2____boxed(lean_object* v_a_4363_){
_start:
{
lean_object* v_res_4364_; 
v_res_4364_ = l___private_Lean_Elab_Deriving_Ord_0__Lean_Elab_Deriving_Ord_initFn_00___x40_Lean_Elab_Deriving_Ord_1187715530____hygCtx___hyg_2_();
return v_res_4364_;
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
