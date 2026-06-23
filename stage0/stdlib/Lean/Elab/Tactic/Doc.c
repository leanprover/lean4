// Lean compiler output
// Module: Lean.Elab.Tactic.Doc
// Imports: import Lean.DocString public import Lean.Elab.Command public import Lean.Parser.Tactic.Doc
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
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_Doc_tacticDocExtExt;
lean_object* l_Lean_TSyntax_getDocString(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_Parser_Tactic_Doc_isTactic(lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_Doc_alternativeOfTactic(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_array_size(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_withExprHover(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_Doc_tacticNameExt;
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_constants(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_Doc_tacticTagExt;
extern lean_object* l_Lean_Parser_parserExtension;
extern lean_object* l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_nestD(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_findDocString_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_Tactic_Doc_getTacticExtensions(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "tactic_extension"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__3_value),LEAN_SCALAR_PTR_LITERAL(226, 244, 145, 122, 23, 135, 199, 68)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Malformed tactic extension command"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__7_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__9_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "` is not a tactic"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "` is an alternative form of `"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Missing documentation comment"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__17_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Doc"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "elabTacticExtension"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 62, 21, 167, 211, 43, 164, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(128, 44, 144, 107, 80, 40, 109, 178)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(17) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0_value),((lean_object*)(((size_t)(43) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1_value),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(17) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(17) << 1) | 1)),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3_value),((lean_object*)(((size_t)(47) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4_value),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___boxed(lean_object*);
static const lean_string_object l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unexpected doc string"};
static const lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__0 = (const lean_object*)&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__0_value;
static lean_once_cell_t l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1;
static const lean_string_object l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "versoCommentBody"};
static const lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__2 = (const lean_object*)&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Malformed 'register_tactic_tag' command"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__2_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "register_tactic_tag"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__4_value),LEAN_SCALAR_PTR_LITERAL(207, 55, 57, 11, 65, 76, 175, 2)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "elabRegisterTacticTag"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 62, 21, 167, 211, 43, 164, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 30, 89, 153, 147, 186, 30, 23)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(46) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(36) << 1) | 1)),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0_value),((lean_object*)(((size_t)(46) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1_value),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4_value),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0;
static lean_once_cell_t l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "$"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(158, 68, 185, 128, 48, 210, 24, 186)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__4_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__5_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__1_value)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__7_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__6_value)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tactic"};
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 76, 33, 121, 85, 143, 17, 224)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__0_value)} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2;
static const lean_closure_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_param___override, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0_value;
static const lean_string_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "• "};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1_value;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2;
static const lean_string_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 4, .m_data = " — \""};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3_value;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4;
static const lean_string_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\""};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5_value;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6;
static const lean_string_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__7 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__7_value;
static const lean_ctor_object l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__7_value)}};
static const lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8_value;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0;
static const lean_array_object l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__1 = (const lean_object*)&l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Available tags: "};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "printTacTags"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 6, 105, 20, 120, 144, 238, 207)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "elabPrintTacTags"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 62, 21, 167, 211, 43, 164, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(202, 38, 126, 200, 28, 172, 117, 128)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "Displays all available tactic tags, with documentation.\n"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(98) << 1) | 1)),((lean_object*)(((size_t)(37) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(130) << 1) | 1)),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0_value),((lean_object*)(((size_t)(37) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1_value),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(98) << 1) | 1)),((lean_object*)(((size_t)(41) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(98) << 1) | 1)),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3_value),((lean_object*)(((size_t)(41) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4_value),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0(lean_object* v___x_1_, lean_object* v___x_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_1_, v___x_2_, v___y_7_, v___y_8_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0___boxed(lean_object* v___x_11_, lean_object* v___x_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0(v___x_11_, v___x_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
return v_res_20_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_21_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__0);
v___x_23_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_23_, 0, v___x_22_);
return v___x_23_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_24_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1);
v___x_25_ = lean_unsigned_to_nat(0u);
v___x_26_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
lean_ctor_set(v___x_26_, 1, v___x_25_);
lean_ctor_set(v___x_26_, 2, v___x_25_);
lean_ctor_set(v___x_26_, 3, v___x_25_);
lean_ctor_set(v___x_26_, 4, v___x_24_);
lean_ctor_set(v___x_26_, 5, v___x_24_);
lean_ctor_set(v___x_26_, 6, v___x_24_);
lean_ctor_set(v___x_26_, 7, v___x_24_);
lean_ctor_set(v___x_26_, 8, v___x_24_);
lean_ctor_set(v___x_26_, 9, v___x_24_);
return v___x_26_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = lean_unsigned_to_nat(32u);
v___x_28_ = lean_mk_empty_array_with_capacity(v___x_27_);
v___x_29_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
return v___x_29_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4(void){
_start:
{
size_t v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_30_ = ((size_t)5ULL);
v___x_31_ = lean_unsigned_to_nat(0u);
v___x_32_ = lean_unsigned_to_nat(32u);
v___x_33_ = lean_mk_empty_array_with_capacity(v___x_32_);
v___x_34_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__3);
v___x_35_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_35_, 0, v___x_34_);
lean_ctor_set(v___x_35_, 1, v___x_33_);
lean_ctor_set(v___x_35_, 2, v___x_31_);
lean_ctor_set(v___x_35_, 3, v___x_31_);
lean_ctor_set_usize(v___x_35_, 4, v___x_30_);
return v___x_35_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_36_ = lean_box(1);
v___x_37_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4);
v___x_38_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__1);
v___x_39_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_39_, 0, v___x_38_);
lean_ctor_set(v___x_39_, 1, v___x_37_);
lean_ctor_set(v___x_39_, 2, v___x_36_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(lean_object* v_msgData_40_, lean_object* v___y_41_){
_start:
{
lean_object* v___x_43_; lean_object* v_env_44_; lean_object* v___x_45_; lean_object* v_scopes_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v_opts_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_43_ = lean_st_ref_get(v___y_41_);
v_env_44_ = lean_ctor_get(v___x_43_, 0);
lean_inc_ref(v_env_44_);
lean_dec(v___x_43_);
v___x_45_ = lean_st_ref_get(v___y_41_);
v_scopes_46_ = lean_ctor_get(v___x_45_, 2);
lean_inc(v_scopes_46_);
lean_dec(v___x_45_);
v___x_47_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_48_ = l_List_head_x21___redArg(v___x_47_, v_scopes_46_);
lean_dec(v_scopes_46_);
v_opts_49_ = lean_ctor_get(v___x_48_, 1);
lean_inc_ref(v_opts_49_);
lean_dec(v___x_48_);
v___x_50_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__2);
v___x_51_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__5);
v___x_52_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_52_, 0, v_env_44_);
lean_ctor_set(v___x_52_, 1, v___x_50_);
lean_ctor_set(v___x_52_, 2, v___x_51_);
lean_ctor_set(v___x_52_, 3, v_opts_49_);
v___x_53_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
lean_ctor_set(v___x_53_, 1, v_msgData_40_);
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___boxed(lean_object* v_msgData_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v_msgData_55_, v___y_56_);
lean_dec(v___y_56_);
return v_res_58_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_box(1);
v___x_60_ = l_Lean_MessageData_ofFormat(v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__2));
v___x_65_ = l_Lean_MessageData_ofFormat(v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3(lean_object* v_x_66_, lean_object* v_x_67_){
_start:
{
if (lean_obj_tag(v_x_67_) == 0)
{
return v_x_66_;
}
else
{
lean_object* v_head_68_; lean_object* v_tail_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_91_; 
v_head_68_ = lean_ctor_get(v_x_67_, 0);
v_tail_69_ = lean_ctor_get(v_x_67_, 1);
v_isSharedCheck_91_ = !lean_is_exclusive(v_x_67_);
if (v_isSharedCheck_91_ == 0)
{
v___x_71_ = v_x_67_;
v_isShared_72_ = v_isSharedCheck_91_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_tail_69_);
lean_inc(v_head_68_);
lean_dec(v_x_67_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_91_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v_before_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_89_; 
v_before_73_ = lean_ctor_get(v_head_68_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v_head_68_);
if (v_isSharedCheck_89_ == 0)
{
lean_object* v_unused_90_; 
v_unused_90_ = lean_ctor_get(v_head_68_, 1);
lean_dec(v_unused_90_);
v___x_75_ = v_head_68_;
v_isShared_76_ = v_isSharedCheck_89_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_before_73_);
lean_dec(v_head_68_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_89_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_77_; lean_object* v___x_79_; 
v___x_77_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_76_ == 0)
{
lean_ctor_set_tag(v___x_75_, 7);
lean_ctor_set(v___x_75_, 1, v___x_77_);
lean_ctor_set(v___x_75_, 0, v_x_66_);
v___x_79_ = v___x_75_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_x_66_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v___x_77_);
v___x_79_ = v_reuseFailAlloc_88_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
lean_object* v___x_80_; lean_object* v___x_82_; 
v___x_80_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__3);
if (v_isShared_72_ == 0)
{
lean_ctor_set_tag(v___x_71_, 7);
lean_ctor_set(v___x_71_, 1, v___x_80_);
lean_ctor_set(v___x_71_, 0, v___x_79_);
v___x_82_ = v___x_71_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v___x_79_);
lean_ctor_set(v_reuseFailAlloc_87_, 1, v___x_80_);
v___x_82_ = v_reuseFailAlloc_87_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_83_ = l_Lean_MessageData_ofSyntax(v_before_73_);
v___x_84_ = l_Lean_indentD(v___x_83_);
v___x_85_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_82_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v_x_66_ = v___x_85_;
v_x_67_ = v_tail_69_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(lean_object* v_opts_92_, lean_object* v_opt_93_){
_start:
{
lean_object* v_name_94_; lean_object* v_defValue_95_; lean_object* v_map_96_; lean_object* v___x_97_; 
v_name_94_ = lean_ctor_get(v_opt_93_, 0);
v_defValue_95_ = lean_ctor_get(v_opt_93_, 1);
v_map_96_ = lean_ctor_get(v_opts_92_, 0);
v___x_97_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_96_, v_name_94_);
if (lean_obj_tag(v___x_97_) == 0)
{
uint8_t v___x_98_; 
v___x_98_ = lean_unbox(v_defValue_95_);
return v___x_98_;
}
else
{
lean_object* v_val_99_; 
v_val_99_ = lean_ctor_get(v___x_97_, 0);
lean_inc(v_val_99_);
lean_dec_ref_known(v___x_97_, 1);
if (lean_obj_tag(v_val_99_) == 1)
{
uint8_t v_v_100_; 
v_v_100_ = lean_ctor_get_uint8(v_val_99_, 0);
lean_dec_ref_known(v_val_99_, 0);
return v_v_100_;
}
else
{
uint8_t v___x_101_; 
lean_dec(v_val_99_);
v___x_101_ = lean_unbox(v_defValue_95_);
return v___x_101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2___boxed(lean_object* v_opts_102_, lean_object* v_opt_103_){
_start:
{
uint8_t v_res_104_; lean_object* v_r_105_; 
v_res_104_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(v_opts_102_, v_opt_103_);
lean_dec_ref(v_opt_103_);
lean_dec_ref(v_opts_102_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__1));
v___x_110_ = l_Lean_MessageData_ofFormat(v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(lean_object* v_msgData_111_, lean_object* v_macroStack_112_, lean_object* v___y_113_){
_start:
{
lean_object* v___x_115_; lean_object* v_scopes_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v_opts_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_115_ = lean_st_ref_get(v___y_113_);
v_scopes_116_ = lean_ctor_get(v___x_115_, 2);
lean_inc(v_scopes_116_);
lean_dec(v___x_115_);
v___x_117_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_118_ = l_List_head_x21___redArg(v___x_117_, v_scopes_116_);
lean_dec(v_scopes_116_);
v_opts_119_ = lean_ctor_get(v___x_118_, 1);
lean_inc_ref(v_opts_119_);
lean_dec(v___x_118_);
v___x_120_ = l_Lean_Elab_pp_macroStack;
v___x_121_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(v_opts_119_, v___x_120_);
lean_dec_ref(v_opts_119_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; 
lean_dec(v_macroStack_112_);
v___x_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_122_, 0, v_msgData_111_);
return v___x_122_;
}
else
{
if (lean_obj_tag(v_macroStack_112_) == 0)
{
lean_object* v___x_123_; 
v___x_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_123_, 0, v_msgData_111_);
return v___x_123_;
}
else
{
lean_object* v_head_124_; lean_object* v_after_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_140_; 
v_head_124_ = lean_ctor_get(v_macroStack_112_, 0);
lean_inc(v_head_124_);
v_after_125_ = lean_ctor_get(v_head_124_, 1);
v_isSharedCheck_140_ = !lean_is_exclusive(v_head_124_);
if (v_isSharedCheck_140_ == 0)
{
lean_object* v_unused_141_; 
v_unused_141_ = lean_ctor_get(v_head_124_, 0);
lean_dec(v_unused_141_);
v___x_127_ = v_head_124_;
v_isShared_128_ = v_isSharedCheck_140_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_after_125_);
lean_dec(v_head_124_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_140_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_129_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
if (v_isShared_128_ == 0)
{
lean_ctor_set_tag(v___x_127_, 7);
lean_ctor_set(v___x_127_, 1, v___x_129_);
lean_ctor_set(v___x_127_, 0, v_msgData_111_);
v___x_131_ = v___x_127_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_msgData_111_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v___x_129_);
v___x_131_ = v_reuseFailAlloc_139_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v_msgData_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_132_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___closed__2);
v___x_133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_131_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
v___x_134_ = l_Lean_MessageData_ofSyntax(v_after_125_);
v___x_135_ = l_Lean_indentD(v___x_134_);
v_msgData_136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_136_, 0, v___x_133_);
lean_ctor_set(v_msgData_136_, 1, v___x_135_);
v___x_137_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3(v_msgData_136_, v_macroStack_112_);
v___x_138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
return v___x_138_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_142_, lean_object* v_macroStack_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(v_msgData_142_, v_macroStack_143_, v___y_144_);
lean_dec(v___y_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(lean_object* v_msg_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_Elab_Command_getRef___redArg(v___y_148_);
if (lean_obj_tag(v___x_151_) == 0)
{
lean_object* v_a_152_; lean_object* v_macroStack_153_; lean_object* v___x_154_; lean_object* v_a_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v_a_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_166_; 
v_a_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_a_152_);
lean_dec_ref_known(v___x_151_, 1);
v_macroStack_153_ = lean_ctor_get(v___y_148_, 4);
v___x_154_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v_msg_147_, v___y_149_);
v_a_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_a_155_);
lean_dec_ref(v___x_154_);
v___x_156_ = l_Lean_Elab_getBetterRef(v_a_152_, v_macroStack_153_);
lean_dec(v_a_152_);
lean_inc(v_macroStack_153_);
v___x_157_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(v_a_155_, v_macroStack_153_, v___y_149_);
v_a_158_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_166_ == 0)
{
v___x_160_ = v___x_157_;
v_isShared_161_ = v_isSharedCheck_166_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_a_158_);
lean_dec(v___x_157_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_166_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_156_);
lean_ctor_set(v___x_162_, 1, v_a_158_);
if (v_isShared_161_ == 0)
{
lean_ctor_set_tag(v___x_160_, 1);
lean_ctor_set(v___x_160_, 0, v___x_162_);
v___x_164_ = v___x_160_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
else
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_174_; 
lean_dec_ref(v_msg_147_);
v_a_167_ = lean_ctor_get(v___x_151_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_174_ == 0)
{
v___x_169_ = v___x_151_;
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_151_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_a_167_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg___boxed(lean_object* v_msg_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v_msg_175_, v___y_176_, v___y_177_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(lean_object* v_ref_180_, lean_object* v_msg_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_Lean_Elab_Command_getRef___redArg(v___y_182_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v_fileName_187_; lean_object* v_fileMap_188_; lean_object* v_currRecDepth_189_; lean_object* v_cmdPos_190_; lean_object* v_macroStack_191_; lean_object* v_quotContext_x3f_192_; lean_object* v_currMacroScope_193_; lean_object* v_snap_x3f_194_; lean_object* v_cancelTk_x3f_195_; uint8_t v_suppressElabErrors_196_; lean_object* v_ref_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_a_186_);
lean_dec_ref_known(v___x_185_, 1);
v_fileName_187_ = lean_ctor_get(v___y_182_, 0);
v_fileMap_188_ = lean_ctor_get(v___y_182_, 1);
v_currRecDepth_189_ = lean_ctor_get(v___y_182_, 2);
v_cmdPos_190_ = lean_ctor_get(v___y_182_, 3);
v_macroStack_191_ = lean_ctor_get(v___y_182_, 4);
v_quotContext_x3f_192_ = lean_ctor_get(v___y_182_, 5);
v_currMacroScope_193_ = lean_ctor_get(v___y_182_, 6);
v_snap_x3f_194_ = lean_ctor_get(v___y_182_, 8);
v_cancelTk_x3f_195_ = lean_ctor_get(v___y_182_, 9);
v_suppressElabErrors_196_ = lean_ctor_get_uint8(v___y_182_, sizeof(void*)*10);
v_ref_197_ = l_Lean_replaceRef(v_ref_180_, v_a_186_);
lean_dec(v_a_186_);
lean_inc(v_cancelTk_x3f_195_);
lean_inc(v_snap_x3f_194_);
lean_inc(v_currMacroScope_193_);
lean_inc(v_quotContext_x3f_192_);
lean_inc(v_macroStack_191_);
lean_inc(v_cmdPos_190_);
lean_inc(v_currRecDepth_189_);
lean_inc_ref(v_fileMap_188_);
lean_inc_ref(v_fileName_187_);
v___x_198_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_198_, 0, v_fileName_187_);
lean_ctor_set(v___x_198_, 1, v_fileMap_188_);
lean_ctor_set(v___x_198_, 2, v_currRecDepth_189_);
lean_ctor_set(v___x_198_, 3, v_cmdPos_190_);
lean_ctor_set(v___x_198_, 4, v_macroStack_191_);
lean_ctor_set(v___x_198_, 5, v_quotContext_x3f_192_);
lean_ctor_set(v___x_198_, 6, v_currMacroScope_193_);
lean_ctor_set(v___x_198_, 7, v_ref_197_);
lean_ctor_set(v___x_198_, 8, v_snap_x3f_194_);
lean_ctor_set(v___x_198_, 9, v_cancelTk_x3f_195_);
lean_ctor_set_uint8(v___x_198_, sizeof(void*)*10, v_suppressElabErrors_196_);
v___x_199_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v_msg_181_, v___x_198_, v___y_183_);
lean_dec_ref_known(v___x_198_, 10);
return v___x_199_;
}
else
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
lean_dec_ref(v_msg_181_);
v_a_200_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_185_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_185_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg___boxed(lean_object* v_ref_208_, lean_object* v_msg_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_ref_208_, v_msg_209_, v___y_210_, v___y_211_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
lean_dec(v_ref_208_);
return v_res_213_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5));
v___x_225_ = l_Lean_stringToMessageData(v___x_224_);
return v___x_225_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11));
v___x_237_ = l_Lean_stringToMessageData(v___x_236_);
return v___x_237_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13));
v___x_240_ = l_Lean_stringToMessageData(v___x_239_);
return v___x_240_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15));
v___x_243_ = l_Lean_stringToMessageData(v___x_242_);
return v___x_243_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__17));
v___x_246_ = l_Lean_stringToMessageData(v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension(lean_object* v_x_247_, lean_object* v_a_248_, lean_object* v_a_249_){
_start:
{
lean_object* v___x_251_; uint8_t v___x_252_; 
v___x_251_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4));
lean_inc(v_x_247_);
v___x_252_ = l_Lean_Syntax_isOfKind(v_x_247_, v___x_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; lean_object* v___x_254_; 
lean_dec(v_x_247_);
v___x_253_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6);
v___x_254_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_253_, v_a_248_, v_a_249_);
return v___x_254_;
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_255_ = lean_unsigned_to_nat(0u);
v___x_256_ = l_Lean_Syntax_getArg(v_x_247_, v___x_255_);
lean_inc(v___x_256_);
v___x_257_ = l_Lean_Syntax_matchesNull(v___x_256_, v___x_255_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_258_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_256_);
v___x_259_ = l_Lean_Syntax_matchesNull(v___x_256_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec(v___x_256_);
lean_dec(v_x_247_);
v___x_260_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6);
v___x_261_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_260_, v_a_248_, v_a_249_);
return v___x_261_;
}
else
{
lean_object* v_docs_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v_docs_262_ = l_Lean_Syntax_getArg(v___x_256_, v___x_255_);
lean_dec(v___x_256_);
v___x_263_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8));
lean_inc(v_docs_262_);
v___x_264_ = l_Lean_Syntax_isOfKind(v_docs_262_, v___x_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec(v_docs_262_);
lean_dec(v_x_247_);
v___x_265_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6);
v___x_266_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_265_, v_a_248_, v_a_249_);
return v___x_266_;
}
else
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_267_ = lean_unsigned_to_nat(2u);
v___x_268_ = l_Lean_Syntax_getArg(v_x_247_, v___x_267_);
lean_dec(v_x_247_);
v___x_269_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10));
lean_inc(v___x_268_);
v___x_270_ = l_Lean_Syntax_isOfKind(v___x_268_, v___x_269_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; lean_object* v___x_272_; 
lean_dec(v___x_268_);
lean_dec(v_docs_262_);
v___x_271_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6);
v___x_272_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_271_, v_a_248_, v_a_249_);
return v___x_272_;
}
else
{
lean_object* v___x_273_; lean_object* v___f_274_; lean_object* v___x_275_; 
v___x_273_ = lean_box(0);
lean_inc(v___x_268_);
v___f_274_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0___boxed), 9, 2);
lean_closure_set(v___f_274_, 0, v___x_268_);
lean_closure_set(v___f_274_, 1, v___x_273_);
v___x_275_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_274_, v_a_248_, v_a_249_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_342_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_342_ == 0)
{
v___x_278_ = v___x_275_;
v_isShared_279_ = v_isSharedCheck_342_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_275_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_342_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___y_281_; lean_object* v___y_314_; lean_object* v___y_315_; uint8_t v___y_316_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___x_329_; lean_object* v_env_330_; lean_object* v___x_331_; 
v___x_329_ = lean_st_ref_get(v_a_249_);
v_env_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc_ref(v_env_330_);
lean_dec(v___x_329_);
lean_inc(v_a_276_);
v___x_331_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_330_, v_a_276_);
if (lean_obj_tag(v___x_331_) == 1)
{
lean_object* v_val_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
lean_del_object(v___x_278_);
lean_dec(v_docs_262_);
v_val_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_val_332_);
lean_dec_ref_known(v___x_331_, 1);
v___x_333_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
v___x_334_ = l_Lean_MessageData_ofConstName(v_a_276_, v___x_257_);
v___x_335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_333_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v___x_336_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16);
v___x_337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_335_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = l_Lean_MessageData_ofConstName(v_val_332_, v___x_257_);
v___x_339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_337_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v___x_340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v___x_333_);
v___x_341_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v___x_268_, v___x_340_, v_a_248_, v_a_249_);
lean_dec(v___x_268_);
return v___x_341_;
}
else
{
lean_dec(v___x_331_);
v___y_324_ = v_a_248_;
v___y_325_ = v_a_249_;
goto v___jp_323_;
}
v___jp_280_:
{
lean_object* v___x_282_; lean_object* v_env_283_; lean_object* v_messages_284_; lean_object* v_scopes_285_; lean_object* v_usedQuotCtxts_286_; lean_object* v_nextMacroScope_287_; lean_object* v_maxRecDepth_288_; lean_object* v_ngen_289_; lean_object* v_auxDeclNGen_290_; lean_object* v_infoState_291_; lean_object* v_traceState_292_; lean_object* v_snapshotTasks_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_312_; 
v___x_282_ = lean_st_ref_take(v___y_281_);
v_env_283_ = lean_ctor_get(v___x_282_, 0);
v_messages_284_ = lean_ctor_get(v___x_282_, 1);
v_scopes_285_ = lean_ctor_get(v___x_282_, 2);
v_usedQuotCtxts_286_ = lean_ctor_get(v___x_282_, 3);
v_nextMacroScope_287_ = lean_ctor_get(v___x_282_, 4);
v_maxRecDepth_288_ = lean_ctor_get(v___x_282_, 5);
v_ngen_289_ = lean_ctor_get(v___x_282_, 6);
v_auxDeclNGen_290_ = lean_ctor_get(v___x_282_, 7);
v_infoState_291_ = lean_ctor_get(v___x_282_, 8);
v_traceState_292_ = lean_ctor_get(v___x_282_, 9);
v_snapshotTasks_293_ = lean_ctor_get(v___x_282_, 10);
v_isSharedCheck_312_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_312_ == 0)
{
v___x_295_ = v___x_282_;
v_isShared_296_ = v_isSharedCheck_312_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_snapshotTasks_293_);
lean_inc(v_traceState_292_);
lean_inc(v_infoState_291_);
lean_inc(v_auxDeclNGen_290_);
lean_inc(v_ngen_289_);
lean_inc(v_maxRecDepth_288_);
lean_inc(v_nextMacroScope_287_);
lean_inc(v_usedQuotCtxts_286_);
lean_inc(v_scopes_285_);
lean_inc(v_messages_284_);
lean_inc(v_env_283_);
lean_dec(v___x_282_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_312_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; lean_object* v_toEnvExtension_298_; lean_object* v_asyncMode_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_305_; 
v___x_297_ = l_Lean_Parser_Tactic_Doc_tacticDocExtExt;
v_toEnvExtension_298_ = lean_ctor_get(v___x_297_, 0);
v_asyncMode_299_ = lean_ctor_get(v_toEnvExtension_298_, 2);
v___x_300_ = l_Lean_TSyntax_getDocString(v_docs_262_);
lean_dec(v_docs_262_);
v___x_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_301_, 0, v_a_276_);
lean_ctor_set(v___x_301_, 1, v___x_300_);
v___x_302_ = lean_box(0);
v___x_303_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_297_, v_env_283_, v___x_301_, v_asyncMode_299_, v___x_302_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_303_);
v___x_305_ = v___x_295_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_303_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v_messages_284_);
lean_ctor_set(v_reuseFailAlloc_311_, 2, v_scopes_285_);
lean_ctor_set(v_reuseFailAlloc_311_, 3, v_usedQuotCtxts_286_);
lean_ctor_set(v_reuseFailAlloc_311_, 4, v_nextMacroScope_287_);
lean_ctor_set(v_reuseFailAlloc_311_, 5, v_maxRecDepth_288_);
lean_ctor_set(v_reuseFailAlloc_311_, 6, v_ngen_289_);
lean_ctor_set(v_reuseFailAlloc_311_, 7, v_auxDeclNGen_290_);
lean_ctor_set(v_reuseFailAlloc_311_, 8, v_infoState_291_);
lean_ctor_set(v_reuseFailAlloc_311_, 9, v_traceState_292_);
lean_ctor_set(v_reuseFailAlloc_311_, 10, v_snapshotTasks_293_);
v___x_305_ = v_reuseFailAlloc_311_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_309_; 
v___x_306_ = lean_st_ref_set(v___y_281_, v___x_305_);
v___x_307_ = lean_box(0);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 0, v___x_307_);
v___x_309_ = v___x_278_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v___x_307_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
}
v___jp_313_:
{
if (v___y_316_ == 0)
{
lean_dec(v___x_268_);
v___y_281_ = v___y_315_;
goto v___jp_280_;
}
else
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
lean_del_object(v___x_278_);
lean_dec(v_docs_262_);
v___x_317_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
v___x_318_ = l_Lean_MessageData_ofConstName(v_a_276_, v___x_257_);
v___x_319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_317_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14);
v___x_321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_319_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
v___x_322_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v___x_268_, v___x_321_, v___y_314_, v___y_315_);
lean_dec(v___x_268_);
return v___x_322_;
}
}
v___jp_323_:
{
lean_object* v___x_326_; lean_object* v_env_327_; uint8_t v___x_328_; 
v___x_326_ = lean_st_ref_get(v___y_325_);
v_env_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc_ref(v_env_327_);
lean_dec(v___x_326_);
v___x_328_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_327_, v_a_276_);
if (v___x_328_ == 0)
{
v___y_314_ = v___y_324_;
v___y_315_ = v___y_325_;
v___y_316_ = v___x_270_;
goto v___jp_313_;
}
else
{
v___y_314_ = v___y_324_;
v___y_315_ = v___y_325_;
v___y_316_ = v___x_257_;
goto v___jp_313_;
}
}
}
}
else
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
lean_dec(v___x_268_);
lean_dec(v_docs_262_);
v_a_343_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_275_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_275_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_351_; lean_object* v_cmd_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
lean_dec(v___x_256_);
v___x_351_ = lean_unsigned_to_nat(1u);
v_cmd_352_ = l_Lean_Syntax_getArg(v_x_247_, v___x_351_);
lean_dec(v_x_247_);
v___x_353_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18);
v___x_354_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_cmd_352_, v___x_353_, v_a_248_, v_a_249_);
lean_dec(v_cmd_352_);
return v___x_354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed(lean_object* v_x_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension(v_x_355_, v_a_356_, v_a_357_);
lean_dec(v_a_357_);
lean_dec_ref(v_a_356_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0(lean_object* v_msgData_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v_msgData_360_, v___y_362_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___boxed(lean_object* v_msgData_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0(v_msgData_365_, v___y_366_, v___y_367_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0(lean_object* v_00_u03b1_370_, lean_object* v_msg_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v_msg_371_, v___y_372_, v___y_373_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___boxed(lean_object* v_00_u03b1_376_, lean_object* v_msg_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0(v_00_u03b1_376_, v_msg_377_, v___y_378_, v___y_379_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1(lean_object* v_00_u03b1_382_, lean_object* v_ref_383_, lean_object* v_msg_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v___x_388_; 
v___x_388_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_ref_383_, v_msg_384_, v___y_385_, v___y_386_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___boxed(lean_object* v_00_u03b1_389_, lean_object* v_ref_390_, lean_object* v_msg_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1(v_00_u03b1_389_, v_ref_390_, v_msg_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v_ref_390_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1(lean_object* v_msgData_396_, lean_object* v_macroStack_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(v_msgData_396_, v_macroStack_397_, v___y_399_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___boxed(lean_object* v_msgData_402_, lean_object* v_macroStack_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1(v_msgData_402_, v_macroStack_403_, v___y_404_, v___y_405_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1(){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_419_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_420_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4));
v___x_421_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_422_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed), 4, 0);
v___x_423_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_419_, v___x_420_, v___x_421_, v___x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___boxed(lean_object* v_a_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3(){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_452_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_453_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6));
v___x_454_ = l_Lean_addBuiltinDeclarationRanges(v___x_452_, v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___boxed(lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
return v_res_456_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__0));
v___x_459_ = l_Lean_stringToMessageData(v___x_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(lean_object* v_stx_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v_val_472_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_unsigned_to_nat(1u);
v___x_480_ = l_Lean_Syntax_getArg(v_stx_461_, v___x_479_);
switch(lean_obj_tag(v___x_480_))
{
case 2:
{
lean_object* v_val_481_; 
lean_dec(v_stx_461_);
v_val_481_ = lean_ctor_get(v___x_480_, 1);
lean_inc_ref(v_val_481_);
lean_dec_ref_known(v___x_480_, 2);
v_val_472_ = v_val_481_;
goto v___jp_471_;
}
case 1:
{
lean_object* v_kind_482_; 
v_kind_482_ = lean_ctor_get(v___x_480_, 1);
lean_inc(v_kind_482_);
if (lean_obj_tag(v_kind_482_) == 1)
{
lean_object* v_pre_483_; 
v_pre_483_ = lean_ctor_get(v_kind_482_, 0);
lean_inc(v_pre_483_);
if (lean_obj_tag(v_pre_483_) == 1)
{
lean_object* v_pre_484_; 
v_pre_484_ = lean_ctor_get(v_pre_483_, 0);
lean_inc(v_pre_484_);
if (lean_obj_tag(v_pre_484_) == 1)
{
lean_object* v_pre_485_; 
v_pre_485_ = lean_ctor_get(v_pre_484_, 0);
lean_inc(v_pre_485_);
if (lean_obj_tag(v_pre_485_) == 1)
{
lean_object* v_pre_486_; 
v_pre_486_ = lean_ctor_get(v_pre_485_, 0);
if (lean_obj_tag(v_pre_486_) == 0)
{
lean_object* v_str_487_; lean_object* v_str_488_; lean_object* v_str_489_; lean_object* v_str_490_; lean_object* v___x_491_; uint8_t v___x_492_; 
v_str_487_ = lean_ctor_get(v_kind_482_, 1);
lean_inc_ref(v_str_487_);
lean_dec_ref_known(v_kind_482_, 2);
v_str_488_ = lean_ctor_get(v_pre_483_, 1);
lean_inc_ref(v_str_488_);
lean_dec_ref_known(v_pre_483_, 2);
v_str_489_ = lean_ctor_get(v_pre_484_, 1);
lean_inc_ref(v_str_489_);
lean_dec_ref_known(v_pre_484_, 2);
v_str_490_ = lean_ctor_get(v_pre_485_, 1);
lean_inc_ref(v_str_490_);
lean_dec_ref_known(v_pre_485_, 2);
v___x_491_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0));
v___x_492_ = lean_string_dec_eq(v_str_490_, v___x_491_);
lean_dec_ref(v_str_490_);
if (v___x_492_ == 0)
{
lean_dec_ref(v_str_489_);
lean_dec_ref(v_str_488_);
lean_dec_ref(v_str_487_);
lean_dec_ref_known(v___x_480_, 3);
goto v___jp_465_;
}
else
{
lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_493_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1));
v___x_494_ = lean_string_dec_eq(v_str_489_, v___x_493_);
lean_dec_ref(v_str_489_);
if (v___x_494_ == 0)
{
lean_dec_ref(v_str_488_);
lean_dec_ref(v_str_487_);
lean_dec_ref_known(v___x_480_, 3);
goto v___jp_465_;
}
else
{
lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_495_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2));
v___x_496_ = lean_string_dec_eq(v_str_488_, v___x_495_);
lean_dec_ref(v_str_488_);
if (v___x_496_ == 0)
{
lean_dec_ref(v_str_487_);
lean_dec_ref_known(v___x_480_, 3);
goto v___jp_465_;
}
else
{
lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_497_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__2));
v___x_498_ = lean_string_dec_eq(v_str_487_, v___x_497_);
lean_dec_ref(v_str_487_);
if (v___x_498_ == 0)
{
lean_dec_ref_known(v___x_480_, 3);
goto v___jp_465_;
}
else
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_unsigned_to_nat(0u);
v___x_500_ = l_Lean_Syntax_getArg(v___x_480_, v___x_499_);
lean_dec_ref_known(v___x_480_, 3);
if (lean_obj_tag(v___x_500_) == 2)
{
lean_object* v_val_501_; 
lean_dec(v_stx_461_);
v_val_501_ = lean_ctor_get(v___x_500_, 1);
lean_inc_ref(v_val_501_);
lean_dec_ref_known(v___x_500_, 2);
v_val_472_ = v_val_501_;
goto v___jp_471_;
}
else
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
lean_dec(v___x_500_);
v___x_502_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1);
lean_inc(v_stx_461_);
v___x_503_ = l_Lean_MessageData_ofSyntax(v_stx_461_);
v___x_504_ = l_Lean_indentD(v___x_503_);
v___x_505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_502_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
v___x_506_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_stx_461_, v___x_505_, v___y_462_, v___y_463_);
lean_dec(v_stx_461_);
return v___x_506_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_pre_485_, 2);
lean_dec_ref_known(v_pre_484_, 2);
lean_dec_ref_known(v_pre_483_, 2);
lean_dec_ref_known(v_kind_482_, 2);
lean_dec_ref_known(v___x_480_, 3);
goto v___jp_465_;
}
}
else
{
lean_dec(v_pre_485_);
lean_dec_ref_known(v_pre_484_, 2);
lean_dec_ref_known(v_pre_483_, 2);
lean_dec_ref_known(v_kind_482_, 2);
lean_dec_ref_known(v___x_480_, 3);
goto v___jp_465_;
}
}
else
{
lean_dec_ref_known(v_pre_483_, 2);
lean_dec(v_pre_484_);
lean_dec_ref_known(v_kind_482_, 2);
lean_dec_ref_known(v___x_480_, 3);
goto v___jp_465_;
}
}
else
{
lean_dec_ref_known(v_kind_482_, 2);
lean_dec(v_pre_483_);
lean_dec_ref_known(v___x_480_, 3);
goto v___jp_465_;
}
}
else
{
lean_dec(v_kind_482_);
lean_dec_ref_known(v___x_480_, 3);
goto v___jp_465_;
}
}
default: 
{
lean_dec(v___x_480_);
goto v___jp_465_;
}
}
v___jp_465_:
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_466_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1);
lean_inc(v_stx_461_);
v___x_467_ = l_Lean_MessageData_ofSyntax(v_stx_461_);
v___x_468_ = l_Lean_indentD(v___x_467_);
v___x_469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_466_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
v___x_470_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_stx_461_, v___x_469_, v___y_462_, v___y_463_);
lean_dec(v_stx_461_);
return v___x_470_;
}
v___jp_471_:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_473_ = lean_unsigned_to_nat(0u);
v___x_474_ = lean_string_utf8_byte_size(v_val_472_);
v___x_475_ = lean_unsigned_to_nat(2u);
v___x_476_ = lean_nat_sub(v___x_474_, v___x_475_);
v___x_477_ = lean_string_utf8_extract(v_val_472_, v___x_473_, v___x_476_);
lean_dec(v___x_476_);
lean_dec_ref(v_val_472_);
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
return v___x_478_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___boxed(lean_object* v_stx_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(v_stx_507_, v___y_508_, v___y_509_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
return v_res_511_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1(void){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0));
v___x_514_ = l_Lean_stringToMessageData(v___x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(lean_object* v_x_524_, lean_object* v_a_525_, lean_object* v_a_526_){
_start:
{
lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v_a_532_; lean_object* v_doc_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_599_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5));
lean_inc(v_x_524_);
v___x_600_ = l_Lean_Syntax_isOfKind(v_x_524_, v___x_599_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; lean_object* v___x_602_; 
lean_dec(v_x_524_);
v___x_601_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_602_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_601_, v_a_525_, v_a_526_);
return v___x_602_;
}
else
{
lean_object* v___x_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_603_ = lean_unsigned_to_nat(0u);
v___x_604_ = l_Lean_Syntax_getArg(v_x_524_, v___x_603_);
v___x_605_ = l_Lean_Syntax_isNone(v___x_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_606_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_604_);
v___x_607_ = l_Lean_Syntax_matchesNull(v___x_604_, v___x_606_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; lean_object* v___x_609_; 
lean_dec(v___x_604_);
lean_dec(v_x_524_);
v___x_608_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_609_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_608_, v_a_525_, v_a_526_);
return v___x_609_;
}
else
{
lean_object* v_doc_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v_doc_610_ = l_Lean_Syntax_getArg(v___x_604_, v___x_603_);
lean_dec(v___x_604_);
v___x_611_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8));
lean_inc(v_doc_610_);
v___x_612_ = l_Lean_Syntax_isOfKind(v_doc_610_, v___x_611_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; lean_object* v___x_614_; 
lean_dec(v_doc_610_);
lean_dec(v_x_524_);
v___x_613_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_614_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_613_, v_a_525_, v_a_526_);
return v___x_614_;
}
else
{
lean_object* v___x_615_; 
v___x_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_615_, 0, v_doc_610_);
v_doc_565_ = v___x_615_;
v___y_566_ = v_a_525_;
v___y_567_ = v_a_526_;
goto v___jp_564_;
}
}
}
else
{
lean_object* v___x_616_; 
lean_dec(v___x_604_);
v___x_616_ = lean_box(0);
v_doc_565_ = v___x_616_;
v___y_566_ = v_a_525_;
v___y_567_ = v_a_526_;
goto v___jp_564_;
}
}
v___jp_528_:
{
lean_object* v___x_533_; lean_object* v_env_534_; lean_object* v_messages_535_; lean_object* v_scopes_536_; lean_object* v_usedQuotCtxts_537_; lean_object* v_nextMacroScope_538_; lean_object* v_maxRecDepth_539_; lean_object* v_ngen_540_; lean_object* v_auxDeclNGen_541_; lean_object* v_infoState_542_; lean_object* v_traceState_543_; lean_object* v_snapshotTasks_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_563_; 
v___x_533_ = lean_st_ref_take(v___y_531_);
v_env_534_ = lean_ctor_get(v___x_533_, 0);
v_messages_535_ = lean_ctor_get(v___x_533_, 1);
v_scopes_536_ = lean_ctor_get(v___x_533_, 2);
v_usedQuotCtxts_537_ = lean_ctor_get(v___x_533_, 3);
v_nextMacroScope_538_ = lean_ctor_get(v___x_533_, 4);
v_maxRecDepth_539_ = lean_ctor_get(v___x_533_, 5);
v_ngen_540_ = lean_ctor_get(v___x_533_, 6);
v_auxDeclNGen_541_ = lean_ctor_get(v___x_533_, 7);
v_infoState_542_ = lean_ctor_get(v___x_533_, 8);
v_traceState_543_ = lean_ctor_get(v___x_533_, 9);
v_snapshotTasks_544_ = lean_ctor_get(v___x_533_, 10);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_563_ == 0)
{
v___x_546_ = v___x_533_;
v_isShared_547_ = v_isSharedCheck_563_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_snapshotTasks_544_);
lean_inc(v_traceState_543_);
lean_inc(v_infoState_542_);
lean_inc(v_auxDeclNGen_541_);
lean_inc(v_ngen_540_);
lean_inc(v_maxRecDepth_539_);
lean_inc(v_nextMacroScope_538_);
lean_inc(v_usedQuotCtxts_537_);
lean_inc(v_scopes_536_);
lean_inc(v_messages_535_);
lean_inc(v_env_534_);
lean_dec(v___x_533_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_563_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v_toEnvExtension_549_; lean_object* v_asyncMode_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_558_; 
v___x_548_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_549_ = lean_ctor_get(v___x_548_, 0);
v_asyncMode_550_ = lean_ctor_get(v_toEnvExtension_549_, 2);
v___x_551_ = l_Lean_TSyntax_getId(v___y_529_);
lean_dec(v___y_529_);
v___x_552_ = l_Lean_TSyntax_getString(v___y_530_);
lean_dec(v___y_530_);
v___x_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_552_);
lean_ctor_set(v___x_553_, 1, v_a_532_);
v___x_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_551_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
v___x_555_ = lean_box(0);
v___x_556_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_548_, v_env_534_, v___x_554_, v_asyncMode_550_, v___x_555_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v___x_556_);
v___x_558_ = v___x_546_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_556_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_messages_535_);
lean_ctor_set(v_reuseFailAlloc_562_, 2, v_scopes_536_);
lean_ctor_set(v_reuseFailAlloc_562_, 3, v_usedQuotCtxts_537_);
lean_ctor_set(v_reuseFailAlloc_562_, 4, v_nextMacroScope_538_);
lean_ctor_set(v_reuseFailAlloc_562_, 5, v_maxRecDepth_539_);
lean_ctor_set(v_reuseFailAlloc_562_, 6, v_ngen_540_);
lean_ctor_set(v_reuseFailAlloc_562_, 7, v_auxDeclNGen_541_);
lean_ctor_set(v_reuseFailAlloc_562_, 8, v_infoState_542_);
lean_ctor_set(v_reuseFailAlloc_562_, 9, v_traceState_543_);
lean_ctor_set(v_reuseFailAlloc_562_, 10, v_snapshotTasks_544_);
v___x_558_ = v_reuseFailAlloc_562_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_559_ = lean_st_ref_set(v___y_531_, v___x_558_);
v___x_560_ = lean_box(0);
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
return v___x_561_;
}
}
}
v___jp_564_:
{
lean_object* v___x_568_; lean_object* v_tag_569_; lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_568_ = lean_unsigned_to_nat(2u);
v_tag_569_ = l_Lean_Syntax_getArg(v_x_524_, v___x_568_);
v___x_570_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10));
lean_inc(v_tag_569_);
v___x_571_ = l_Lean_Syntax_isOfKind(v_tag_569_, v___x_570_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; lean_object* v___x_573_; 
lean_dec(v_tag_569_);
lean_dec(v_doc_565_);
lean_dec(v_x_524_);
v___x_572_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_573_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_572_, v___y_566_, v___y_567_);
return v___x_573_;
}
else
{
lean_object* v___x_574_; lean_object* v_user_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_574_ = lean_unsigned_to_nat(3u);
v_user_575_ = l_Lean_Syntax_getArg(v_x_524_, v___x_574_);
lean_dec(v_x_524_);
v___x_576_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3));
lean_inc(v_user_575_);
v___x_577_ = l_Lean_Syntax_isOfKind(v_user_575_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_578_; lean_object* v___x_579_; 
lean_dec(v_user_575_);
lean_dec(v_tag_569_);
lean_dec(v_doc_565_);
v___x_578_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_579_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_578_, v___y_566_, v___y_567_);
return v___x_579_;
}
else
{
if (lean_obj_tag(v_doc_565_) == 0)
{
lean_object* v___x_580_; 
v___x_580_ = lean_box(0);
v___y_529_ = v_tag_569_;
v___y_530_ = v_user_575_;
v___y_531_ = v___y_567_;
v_a_532_ = v___x_580_;
goto v___jp_528_;
}
else
{
lean_object* v_val_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_598_; 
v_val_581_ = lean_ctor_get(v_doc_565_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v_doc_565_);
if (v_isSharedCheck_598_ == 0)
{
v___x_583_ = v_doc_565_;
v_isShared_584_ = v_isSharedCheck_598_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_val_581_);
lean_dec(v_doc_565_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_598_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(v_val_581_, v___y_566_, v___y_567_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_588_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_a_586_);
lean_dec_ref_known(v___x_585_, 1);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v_a_586_);
v___x_588_ = v___x_583_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
v___y_529_ = v_tag_569_;
v___y_530_ = v_user_575_;
v___y_531_ = v___y_567_;
v_a_532_ = v___x_588_;
goto v___jp_528_;
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
lean_del_object(v___x_583_);
lean_dec(v_user_575_);
lean_dec(v_tag_569_);
v_a_590_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_585_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_585_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed(lean_object* v_x_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(v_x_617_, v_a_618_, v_a_619_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1(){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_630_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_631_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5));
v___x_632_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_633_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed), 4, 0);
v___x_634_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_630_, v___x_631_, v___x_632_, v___x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___boxed(lean_object* v_a_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3(){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_663_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_664_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6));
v___x_665_ = l_Lean_addBuiltinDeclarationRanges(v___x_663_, v___x_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___boxed(lean_object* v_a_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(lean_object* v___x_668_, lean_object* v_x_669_){
_start:
{
if (lean_obj_tag(v_x_669_) == 0)
{
lean_object* v___x_670_; 
v___x_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_668_);
return v___x_670_;
}
else
{
lean_dec_ref(v___x_668_);
lean_inc_ref(v_x_669_);
return v_x_669_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0___boxed(lean_object* v___x_671_, lean_object* v_x_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_671_, v_x_672_);
lean_dec(v_x_672_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(lean_object* v___x_674_, lean_object* v_k_675_, lean_object* v_t_676_){
_start:
{
if (lean_obj_tag(v_t_676_) == 0)
{
lean_object* v_size_677_; lean_object* v_k_678_; lean_object* v_v_679_; lean_object* v_l_680_; lean_object* v_r_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_1007_; 
v_size_677_ = lean_ctor_get(v_t_676_, 0);
v_k_678_ = lean_ctor_get(v_t_676_, 1);
v_v_679_ = lean_ctor_get(v_t_676_, 2);
v_l_680_ = lean_ctor_get(v_t_676_, 3);
v_r_681_ = lean_ctor_get(v_t_676_, 4);
v_isSharedCheck_1007_ = !lean_is_exclusive(v_t_676_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_683_ = v_t_676_;
v_isShared_684_ = v_isSharedCheck_1007_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_r_681_);
lean_inc(v_l_680_);
lean_inc(v_v_679_);
lean_inc(v_k_678_);
lean_inc(v_size_677_);
lean_dec(v_t_676_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_1007_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
uint8_t v___x_685_; 
v___x_685_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_675_, v_k_678_);
switch(v___x_685_)
{
case 0:
{
lean_object* v_impl_686_; lean_object* v___x_687_; 
lean_del_object(v___x_683_);
lean_dec(v_size_677_);
v_impl_686_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_674_, v_k_675_, v_l_680_);
v___x_687_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_678_, v_v_679_, v_impl_686_, v_r_681_);
return v___x_687_;
}
case 1:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
lean_dec(v_k_678_);
v___x_688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_688_, 0, v_v_679_);
v___x_689_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_674_, v___x_688_);
lean_dec_ref_known(v___x_688_, 1);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_del_object(v___x_683_);
lean_dec(v_size_677_);
lean_dec(v_k_675_);
if (lean_obj_tag(v_l_680_) == 0)
{
if (lean_obj_tag(v_r_681_) == 0)
{
lean_object* v_size_690_; lean_object* v_k_691_; lean_object* v_v_692_; lean_object* v_l_693_; lean_object* v_r_694_; lean_object* v_size_695_; lean_object* v_k_696_; lean_object* v_v_697_; lean_object* v_l_698_; lean_object* v_r_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
v_size_690_ = lean_ctor_get(v_l_680_, 0);
v_k_691_ = lean_ctor_get(v_l_680_, 1);
v_v_692_ = lean_ctor_get(v_l_680_, 2);
v_l_693_ = lean_ctor_get(v_l_680_, 3);
v_r_694_ = lean_ctor_get(v_l_680_, 4);
lean_inc(v_r_694_);
v_size_695_ = lean_ctor_get(v_r_681_, 0);
v_k_696_ = lean_ctor_get(v_r_681_, 1);
v_v_697_ = lean_ctor_get(v_r_681_, 2);
v_l_698_ = lean_ctor_get(v_r_681_, 3);
lean_inc(v_l_698_);
v_r_699_ = lean_ctor_get(v_r_681_, 4);
v___x_700_ = lean_unsigned_to_nat(1u);
v___x_701_ = lean_nat_dec_lt(v_size_690_, v_size_695_);
if (v___x_701_ == 0)
{
lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_837_; 
lean_inc(v_l_693_);
lean_inc(v_v_692_);
lean_inc(v_k_691_);
v_isSharedCheck_837_ = !lean_is_exclusive(v_l_680_);
if (v_isSharedCheck_837_ == 0)
{
lean_object* v_unused_838_; lean_object* v_unused_839_; lean_object* v_unused_840_; lean_object* v_unused_841_; lean_object* v_unused_842_; 
v_unused_838_ = lean_ctor_get(v_l_680_, 4);
lean_dec(v_unused_838_);
v_unused_839_ = lean_ctor_get(v_l_680_, 3);
lean_dec(v_unused_839_);
v_unused_840_ = lean_ctor_get(v_l_680_, 2);
lean_dec(v_unused_840_);
v_unused_841_ = lean_ctor_get(v_l_680_, 1);
lean_dec(v_unused_841_);
v_unused_842_ = lean_ctor_get(v_l_680_, 0);
lean_dec(v_unused_842_);
v___x_703_ = v_l_680_;
v_isShared_704_ = v_isSharedCheck_837_;
goto v_resetjp_702_;
}
else
{
lean_dec(v_l_680_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_837_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; lean_object* v_tree_706_; 
v___x_705_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_691_, v_v_692_, v_l_693_, v_r_694_);
v_tree_706_ = lean_ctor_get(v___x_705_, 2);
lean_inc(v_tree_706_);
if (lean_obj_tag(v_tree_706_) == 0)
{
lean_object* v_k_707_; lean_object* v_v_708_; lean_object* v_size_709_; lean_object* v___x_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
v_k_707_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_k_707_);
v_v_708_ = lean_ctor_get(v___x_705_, 1);
lean_inc(v_v_708_);
lean_dec_ref(v___x_705_);
v_size_709_ = lean_ctor_get(v_tree_706_, 0);
v___x_710_ = lean_unsigned_to_nat(3u);
v___x_711_ = lean_nat_mul(v___x_710_, v_size_709_);
v___x_712_ = lean_nat_dec_lt(v___x_711_, v_size_695_);
lean_dec(v___x_711_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
lean_dec(v_l_698_);
v___x_713_ = lean_nat_add(v___x_700_, v_size_709_);
v___x_714_ = lean_nat_add(v___x_713_, v_size_695_);
lean_dec(v___x_713_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 4, v_r_681_);
lean_ctor_set(v___x_703_, 3, v_tree_706_);
lean_ctor_set(v___x_703_, 2, v_v_708_);
lean_ctor_set(v___x_703_, 1, v_k_707_);
lean_ctor_set(v___x_703_, 0, v___x_714_);
v___x_716_ = v___x_703_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v_k_707_);
lean_ctor_set(v_reuseFailAlloc_717_, 2, v_v_708_);
lean_ctor_set(v_reuseFailAlloc_717_, 3, v_tree_706_);
lean_ctor_set(v_reuseFailAlloc_717_, 4, v_r_681_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
else
{
lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_772_; 
lean_inc(v_r_699_);
lean_inc(v_v_697_);
lean_inc(v_k_696_);
lean_inc(v_size_695_);
v_isSharedCheck_772_ = !lean_is_exclusive(v_r_681_);
if (v_isSharedCheck_772_ == 0)
{
lean_object* v_unused_773_; lean_object* v_unused_774_; lean_object* v_unused_775_; lean_object* v_unused_776_; lean_object* v_unused_777_; 
v_unused_773_ = lean_ctor_get(v_r_681_, 4);
lean_dec(v_unused_773_);
v_unused_774_ = lean_ctor_get(v_r_681_, 3);
lean_dec(v_unused_774_);
v_unused_775_ = lean_ctor_get(v_r_681_, 2);
lean_dec(v_unused_775_);
v_unused_776_ = lean_ctor_get(v_r_681_, 1);
lean_dec(v_unused_776_);
v_unused_777_ = lean_ctor_get(v_r_681_, 0);
lean_dec(v_unused_777_);
v___x_719_ = v_r_681_;
v_isShared_720_ = v_isSharedCheck_772_;
goto v_resetjp_718_;
}
else
{
lean_dec(v_r_681_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_772_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v_size_721_; lean_object* v_k_722_; lean_object* v_v_723_; lean_object* v_l_724_; lean_object* v_r_725_; lean_object* v_size_726_; lean_object* v___x_727_; lean_object* v___x_728_; uint8_t v___x_729_; 
v_size_721_ = lean_ctor_get(v_l_698_, 0);
v_k_722_ = lean_ctor_get(v_l_698_, 1);
v_v_723_ = lean_ctor_get(v_l_698_, 2);
v_l_724_ = lean_ctor_get(v_l_698_, 3);
v_r_725_ = lean_ctor_get(v_l_698_, 4);
v_size_726_ = lean_ctor_get(v_r_699_, 0);
v___x_727_ = lean_unsigned_to_nat(2u);
v___x_728_ = lean_nat_mul(v___x_727_, v_size_726_);
v___x_729_ = lean_nat_dec_lt(v_size_721_, v___x_728_);
lean_dec(v___x_728_);
if (v___x_729_ == 0)
{
lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_757_; 
lean_inc(v_r_725_);
lean_inc(v_l_724_);
lean_inc(v_v_723_);
lean_inc(v_k_722_);
v_isSharedCheck_757_ = !lean_is_exclusive(v_l_698_);
if (v_isSharedCheck_757_ == 0)
{
lean_object* v_unused_758_; lean_object* v_unused_759_; lean_object* v_unused_760_; lean_object* v_unused_761_; lean_object* v_unused_762_; 
v_unused_758_ = lean_ctor_get(v_l_698_, 4);
lean_dec(v_unused_758_);
v_unused_759_ = lean_ctor_get(v_l_698_, 3);
lean_dec(v_unused_759_);
v_unused_760_ = lean_ctor_get(v_l_698_, 2);
lean_dec(v_unused_760_);
v_unused_761_ = lean_ctor_get(v_l_698_, 1);
lean_dec(v_unused_761_);
v_unused_762_ = lean_ctor_get(v_l_698_, 0);
lean_dec(v_unused_762_);
v___x_731_ = v_l_698_;
v_isShared_732_ = v_isSharedCheck_757_;
goto v_resetjp_730_;
}
else
{
lean_dec(v_l_698_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_757_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_747_; 
v___x_733_ = lean_nat_add(v___x_700_, v_size_709_);
v___x_734_ = lean_nat_add(v___x_733_, v_size_695_);
lean_dec(v_size_695_);
if (lean_obj_tag(v_l_724_) == 0)
{
lean_object* v_size_755_; 
v_size_755_ = lean_ctor_get(v_l_724_, 0);
lean_inc(v_size_755_);
v___y_747_ = v_size_755_;
goto v___jp_746_;
}
else
{
lean_object* v___x_756_; 
v___x_756_ = lean_unsigned_to_nat(0u);
v___y_747_ = v___x_756_;
goto v___jp_746_;
}
v___jp_735_:
{
lean_object* v___x_739_; lean_object* v___x_741_; 
v___x_739_ = lean_nat_add(v___y_736_, v___y_738_);
lean_dec(v___y_738_);
lean_dec(v___y_736_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 4, v_r_699_);
lean_ctor_set(v___x_731_, 3, v_r_725_);
lean_ctor_set(v___x_731_, 2, v_v_697_);
lean_ctor_set(v___x_731_, 1, v_k_696_);
lean_ctor_set(v___x_731_, 0, v___x_739_);
v___x_741_ = v___x_731_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_739_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_k_696_);
lean_ctor_set(v_reuseFailAlloc_745_, 2, v_v_697_);
lean_ctor_set(v_reuseFailAlloc_745_, 3, v_r_725_);
lean_ctor_set(v_reuseFailAlloc_745_, 4, v_r_699_);
v___x_741_ = v_reuseFailAlloc_745_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_object* v___x_743_; 
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 4, v___x_741_);
lean_ctor_set(v___x_719_, 3, v___y_737_);
lean_ctor_set(v___x_719_, 2, v_v_723_);
lean_ctor_set(v___x_719_, 1, v_k_722_);
lean_ctor_set(v___x_719_, 0, v___x_734_);
v___x_743_ = v___x_719_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_734_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_k_722_);
lean_ctor_set(v_reuseFailAlloc_744_, 2, v_v_723_);
lean_ctor_set(v_reuseFailAlloc_744_, 3, v___y_737_);
lean_ctor_set(v_reuseFailAlloc_744_, 4, v___x_741_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
v___jp_746_:
{
lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_748_ = lean_nat_add(v___x_733_, v___y_747_);
lean_dec(v___y_747_);
lean_dec(v___x_733_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 4, v_l_724_);
lean_ctor_set(v___x_703_, 3, v_tree_706_);
lean_ctor_set(v___x_703_, 2, v_v_708_);
lean_ctor_set(v___x_703_, 1, v_k_707_);
lean_ctor_set(v___x_703_, 0, v___x_748_);
v___x_750_ = v___x_703_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_k_707_);
lean_ctor_set(v_reuseFailAlloc_754_, 2, v_v_708_);
lean_ctor_set(v_reuseFailAlloc_754_, 3, v_tree_706_);
lean_ctor_set(v_reuseFailAlloc_754_, 4, v_l_724_);
v___x_750_ = v_reuseFailAlloc_754_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_751_; 
v___x_751_ = lean_nat_add(v___x_700_, v_size_726_);
if (lean_obj_tag(v_r_725_) == 0)
{
lean_object* v_size_752_; 
v_size_752_ = lean_ctor_get(v_r_725_, 0);
lean_inc(v_size_752_);
v___y_736_ = v___x_751_;
v___y_737_ = v___x_750_;
v___y_738_ = v_size_752_;
goto v___jp_735_;
}
else
{
lean_object* v___x_753_; 
v___x_753_ = lean_unsigned_to_nat(0u);
v___y_736_ = v___x_751_;
v___y_737_ = v___x_750_;
v___y_738_ = v___x_753_;
goto v___jp_735_;
}
}
}
}
}
else
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_767_; 
v___x_763_ = lean_nat_add(v___x_700_, v_size_709_);
v___x_764_ = lean_nat_add(v___x_763_, v_size_695_);
lean_dec(v_size_695_);
v___x_765_ = lean_nat_add(v___x_763_, v_size_721_);
lean_dec(v___x_763_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 4, v_l_698_);
lean_ctor_set(v___x_719_, 3, v_tree_706_);
lean_ctor_set(v___x_719_, 2, v_v_708_);
lean_ctor_set(v___x_719_, 1, v_k_707_);
lean_ctor_set(v___x_719_, 0, v___x_765_);
v___x_767_ = v___x_719_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_k_707_);
lean_ctor_set(v_reuseFailAlloc_771_, 2, v_v_708_);
lean_ctor_set(v_reuseFailAlloc_771_, 3, v_tree_706_);
lean_ctor_set(v_reuseFailAlloc_771_, 4, v_l_698_);
v___x_767_ = v_reuseFailAlloc_771_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
lean_object* v___x_769_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 4, v_r_699_);
lean_ctor_set(v___x_703_, 3, v___x_767_);
lean_ctor_set(v___x_703_, 2, v_v_697_);
lean_ctor_set(v___x_703_, 1, v_k_696_);
lean_ctor_set(v___x_703_, 0, v___x_764_);
v___x_769_ = v___x_703_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_764_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_k_696_);
lean_ctor_set(v_reuseFailAlloc_770_, 2, v_v_697_);
lean_ctor_set(v_reuseFailAlloc_770_, 3, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_770_, 4, v_r_699_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
}
else
{
lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_831_; 
lean_inc(v_r_699_);
lean_inc(v_v_697_);
lean_inc(v_k_696_);
lean_inc(v_size_695_);
v_isSharedCheck_831_ = !lean_is_exclusive(v_r_681_);
if (v_isSharedCheck_831_ == 0)
{
lean_object* v_unused_832_; lean_object* v_unused_833_; lean_object* v_unused_834_; lean_object* v_unused_835_; lean_object* v_unused_836_; 
v_unused_832_ = lean_ctor_get(v_r_681_, 4);
lean_dec(v_unused_832_);
v_unused_833_ = lean_ctor_get(v_r_681_, 3);
lean_dec(v_unused_833_);
v_unused_834_ = lean_ctor_get(v_r_681_, 2);
lean_dec(v_unused_834_);
v_unused_835_ = lean_ctor_get(v_r_681_, 1);
lean_dec(v_unused_835_);
v_unused_836_ = lean_ctor_get(v_r_681_, 0);
lean_dec(v_unused_836_);
v___x_779_ = v_r_681_;
v_isShared_780_ = v_isSharedCheck_831_;
goto v_resetjp_778_;
}
else
{
lean_dec(v_r_681_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_831_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
if (lean_obj_tag(v_l_698_) == 0)
{
if (lean_obj_tag(v_r_699_) == 0)
{
lean_object* v_k_781_; lean_object* v_v_782_; lean_object* v_size_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_787_; 
v_k_781_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_k_781_);
v_v_782_ = lean_ctor_get(v___x_705_, 1);
lean_inc(v_v_782_);
lean_dec_ref(v___x_705_);
v_size_783_ = lean_ctor_get(v_l_698_, 0);
v___x_784_ = lean_nat_add(v___x_700_, v_size_695_);
lean_dec(v_size_695_);
v___x_785_ = lean_nat_add(v___x_700_, v_size_783_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 4, v_l_698_);
lean_ctor_set(v___x_779_, 3, v_tree_706_);
lean_ctor_set(v___x_779_, 2, v_v_782_);
lean_ctor_set(v___x_779_, 1, v_k_781_);
lean_ctor_set(v___x_779_, 0, v___x_785_);
v___x_787_ = v___x_779_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_k_781_);
lean_ctor_set(v_reuseFailAlloc_791_, 2, v_v_782_);
lean_ctor_set(v_reuseFailAlloc_791_, 3, v_tree_706_);
lean_ctor_set(v_reuseFailAlloc_791_, 4, v_l_698_);
v___x_787_ = v_reuseFailAlloc_791_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
lean_object* v___x_789_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 4, v_r_699_);
lean_ctor_set(v___x_703_, 3, v___x_787_);
lean_ctor_set(v___x_703_, 2, v_v_697_);
lean_ctor_set(v___x_703_, 1, v_k_696_);
lean_ctor_set(v___x_703_, 0, v___x_784_);
v___x_789_ = v___x_703_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_784_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_k_696_);
lean_ctor_set(v_reuseFailAlloc_790_, 2, v_v_697_);
lean_ctor_set(v_reuseFailAlloc_790_, 3, v___x_787_);
lean_ctor_set(v_reuseFailAlloc_790_, 4, v_r_699_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
else
{
lean_object* v_k_792_; lean_object* v_v_793_; lean_object* v_k_794_; lean_object* v_v_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_809_; 
lean_dec(v_size_695_);
v_k_792_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_k_792_);
v_v_793_ = lean_ctor_get(v___x_705_, 1);
lean_inc(v_v_793_);
lean_dec_ref(v___x_705_);
v_k_794_ = lean_ctor_get(v_l_698_, 1);
v_v_795_ = lean_ctor_get(v_l_698_, 2);
v_isSharedCheck_809_ = !lean_is_exclusive(v_l_698_);
if (v_isSharedCheck_809_ == 0)
{
lean_object* v_unused_810_; lean_object* v_unused_811_; lean_object* v_unused_812_; 
v_unused_810_ = lean_ctor_get(v_l_698_, 4);
lean_dec(v_unused_810_);
v_unused_811_ = lean_ctor_get(v_l_698_, 3);
lean_dec(v_unused_811_);
v_unused_812_ = lean_ctor_get(v_l_698_, 0);
lean_dec(v_unused_812_);
v___x_797_ = v_l_698_;
v_isShared_798_ = v_isSharedCheck_809_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_v_795_);
lean_inc(v_k_794_);
lean_dec(v_l_698_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_809_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; lean_object* v___x_801_; 
v___x_799_ = lean_unsigned_to_nat(3u);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 4, v_r_699_);
lean_ctor_set(v___x_797_, 3, v_r_699_);
lean_ctor_set(v___x_797_, 2, v_v_793_);
lean_ctor_set(v___x_797_, 1, v_k_792_);
lean_ctor_set(v___x_797_, 0, v___x_700_);
v___x_801_ = v___x_797_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_k_792_);
lean_ctor_set(v_reuseFailAlloc_808_, 2, v_v_793_);
lean_ctor_set(v_reuseFailAlloc_808_, 3, v_r_699_);
lean_ctor_set(v_reuseFailAlloc_808_, 4, v_r_699_);
v___x_801_ = v_reuseFailAlloc_808_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_803_; 
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 3, v_r_699_);
lean_ctor_set(v___x_779_, 0, v___x_700_);
v___x_803_ = v___x_779_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_k_696_);
lean_ctor_set(v_reuseFailAlloc_807_, 2, v_v_697_);
lean_ctor_set(v_reuseFailAlloc_807_, 3, v_r_699_);
lean_ctor_set(v_reuseFailAlloc_807_, 4, v_r_699_);
v___x_803_ = v_reuseFailAlloc_807_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_805_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 4, v___x_803_);
lean_ctor_set(v___x_703_, 3, v___x_801_);
lean_ctor_set(v___x_703_, 2, v_v_795_);
lean_ctor_set(v___x_703_, 1, v_k_794_);
lean_ctor_set(v___x_703_, 0, v___x_799_);
v___x_805_ = v___x_703_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v_k_794_);
lean_ctor_set(v_reuseFailAlloc_806_, 2, v_v_795_);
lean_ctor_set(v_reuseFailAlloc_806_, 3, v___x_801_);
lean_ctor_set(v_reuseFailAlloc_806_, 4, v___x_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_699_) == 0)
{
lean_object* v_k_813_; lean_object* v_v_814_; lean_object* v___x_815_; lean_object* v___x_817_; 
lean_dec(v_size_695_);
v_k_813_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_k_813_);
v_v_814_ = lean_ctor_get(v___x_705_, 1);
lean_inc(v_v_814_);
lean_dec_ref(v___x_705_);
v___x_815_ = lean_unsigned_to_nat(3u);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 4, v_l_698_);
lean_ctor_set(v___x_779_, 2, v_v_814_);
lean_ctor_set(v___x_779_, 1, v_k_813_);
lean_ctor_set(v___x_779_, 0, v___x_700_);
v___x_817_ = v___x_779_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_k_813_);
lean_ctor_set(v_reuseFailAlloc_821_, 2, v_v_814_);
lean_ctor_set(v_reuseFailAlloc_821_, 3, v_l_698_);
lean_ctor_set(v_reuseFailAlloc_821_, 4, v_l_698_);
v___x_817_ = v_reuseFailAlloc_821_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_819_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 4, v_r_699_);
lean_ctor_set(v___x_703_, 3, v___x_817_);
lean_ctor_set(v___x_703_, 2, v_v_697_);
lean_ctor_set(v___x_703_, 1, v_k_696_);
lean_ctor_set(v___x_703_, 0, v___x_815_);
v___x_819_ = v___x_703_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_815_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_k_696_);
lean_ctor_set(v_reuseFailAlloc_820_, 2, v_v_697_);
lean_ctor_set(v_reuseFailAlloc_820_, 3, v___x_817_);
lean_ctor_set(v_reuseFailAlloc_820_, 4, v_r_699_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
else
{
lean_object* v_k_822_; lean_object* v_v_823_; lean_object* v___x_825_; 
v_k_822_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_k_822_);
v_v_823_ = lean_ctor_get(v___x_705_, 1);
lean_inc(v_v_823_);
lean_dec_ref(v___x_705_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 3, v_r_699_);
v___x_825_ = v___x_779_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_size_695_);
lean_ctor_set(v_reuseFailAlloc_830_, 1, v_k_696_);
lean_ctor_set(v_reuseFailAlloc_830_, 2, v_v_697_);
lean_ctor_set(v_reuseFailAlloc_830_, 3, v_r_699_);
lean_ctor_set(v_reuseFailAlloc_830_, 4, v_r_699_);
v___x_825_ = v_reuseFailAlloc_830_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_826_ = lean_unsigned_to_nat(2u);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 4, v___x_825_);
lean_ctor_set(v___x_703_, 3, v_r_699_);
lean_ctor_set(v___x_703_, 2, v_v_823_);
lean_ctor_set(v___x_703_, 1, v_k_822_);
lean_ctor_set(v___x_703_, 0, v___x_826_);
v___x_828_ = v___x_703_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v_k_822_);
lean_ctor_set(v_reuseFailAlloc_829_, 2, v_v_823_);
lean_ctor_set(v_reuseFailAlloc_829_, 3, v_r_699_);
lean_ctor_set(v_reuseFailAlloc_829_, 4, v___x_825_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_995_; 
lean_inc(v_r_699_);
lean_inc(v_v_697_);
lean_inc(v_k_696_);
v_isSharedCheck_995_ = !lean_is_exclusive(v_r_681_);
if (v_isSharedCheck_995_ == 0)
{
lean_object* v_unused_996_; lean_object* v_unused_997_; lean_object* v_unused_998_; lean_object* v_unused_999_; lean_object* v_unused_1000_; 
v_unused_996_ = lean_ctor_get(v_r_681_, 4);
lean_dec(v_unused_996_);
v_unused_997_ = lean_ctor_get(v_r_681_, 3);
lean_dec(v_unused_997_);
v_unused_998_ = lean_ctor_get(v_r_681_, 2);
lean_dec(v_unused_998_);
v_unused_999_ = lean_ctor_get(v_r_681_, 1);
lean_dec(v_unused_999_);
v_unused_1000_ = lean_ctor_get(v_r_681_, 0);
lean_dec(v_unused_1000_);
v___x_844_ = v_r_681_;
v_isShared_845_ = v_isSharedCheck_995_;
goto v_resetjp_843_;
}
else
{
lean_dec(v_r_681_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_995_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v_tree_847_; 
v___x_846_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_696_, v_v_697_, v_l_698_, v_r_699_);
v_tree_847_ = lean_ctor_get(v___x_846_, 2);
lean_inc(v_tree_847_);
if (lean_obj_tag(v_tree_847_) == 0)
{
lean_object* v_k_848_; lean_object* v_v_849_; lean_object* v_size_850_; lean_object* v___x_851_; lean_object* v___x_852_; uint8_t v___x_853_; 
v_k_848_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_k_848_);
v_v_849_ = lean_ctor_get(v___x_846_, 1);
lean_inc(v_v_849_);
lean_dec_ref(v___x_846_);
v_size_850_ = lean_ctor_get(v_tree_847_, 0);
v___x_851_ = lean_unsigned_to_nat(3u);
v___x_852_ = lean_nat_mul(v___x_851_, v_size_850_);
v___x_853_ = lean_nat_dec_lt(v___x_852_, v_size_690_);
lean_dec(v___x_852_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_857_; 
lean_dec(v_r_694_);
v___x_854_ = lean_nat_add(v___x_700_, v_size_690_);
v___x_855_ = lean_nat_add(v___x_854_, v_size_850_);
lean_dec(v___x_854_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 4, v_tree_847_);
lean_ctor_set(v___x_844_, 3, v_l_680_);
lean_ctor_set(v___x_844_, 2, v_v_849_);
lean_ctor_set(v___x_844_, 1, v_k_848_);
lean_ctor_set(v___x_844_, 0, v___x_855_);
v___x_857_ = v___x_844_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v_k_848_);
lean_ctor_set(v_reuseFailAlloc_858_, 2, v_v_849_);
lean_ctor_set(v_reuseFailAlloc_858_, 3, v_l_680_);
lean_ctor_set(v_reuseFailAlloc_858_, 4, v_tree_847_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
else
{
lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_924_; 
lean_inc(v_l_693_);
lean_inc(v_v_692_);
lean_inc(v_k_691_);
lean_inc(v_size_690_);
v_isSharedCheck_924_ = !lean_is_exclusive(v_l_680_);
if (v_isSharedCheck_924_ == 0)
{
lean_object* v_unused_925_; lean_object* v_unused_926_; lean_object* v_unused_927_; lean_object* v_unused_928_; lean_object* v_unused_929_; 
v_unused_925_ = lean_ctor_get(v_l_680_, 4);
lean_dec(v_unused_925_);
v_unused_926_ = lean_ctor_get(v_l_680_, 3);
lean_dec(v_unused_926_);
v_unused_927_ = lean_ctor_get(v_l_680_, 2);
lean_dec(v_unused_927_);
v_unused_928_ = lean_ctor_get(v_l_680_, 1);
lean_dec(v_unused_928_);
v_unused_929_ = lean_ctor_get(v_l_680_, 0);
lean_dec(v_unused_929_);
v___x_860_ = v_l_680_;
v_isShared_861_ = v_isSharedCheck_924_;
goto v_resetjp_859_;
}
else
{
lean_dec(v_l_680_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_924_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v_size_862_; lean_object* v_size_863_; lean_object* v_k_864_; lean_object* v_v_865_; lean_object* v_l_866_; lean_object* v_r_867_; lean_object* v___x_868_; lean_object* v___x_869_; uint8_t v___x_870_; 
v_size_862_ = lean_ctor_get(v_l_693_, 0);
v_size_863_ = lean_ctor_get(v_r_694_, 0);
v_k_864_ = lean_ctor_get(v_r_694_, 1);
v_v_865_ = lean_ctor_get(v_r_694_, 2);
v_l_866_ = lean_ctor_get(v_r_694_, 3);
v_r_867_ = lean_ctor_get(v_r_694_, 4);
v___x_868_ = lean_unsigned_to_nat(2u);
v___x_869_ = lean_nat_mul(v___x_868_, v_size_862_);
v___x_870_ = lean_nat_dec_lt(v_size_863_, v___x_869_);
lean_dec(v___x_869_);
if (v___x_870_ == 0)
{
lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_908_; 
lean_inc(v_r_867_);
lean_inc(v_l_866_);
lean_inc(v_v_865_);
lean_inc(v_k_864_);
lean_del_object(v___x_860_);
v_isSharedCheck_908_ = !lean_is_exclusive(v_r_694_);
if (v_isSharedCheck_908_ == 0)
{
lean_object* v_unused_909_; lean_object* v_unused_910_; lean_object* v_unused_911_; lean_object* v_unused_912_; lean_object* v_unused_913_; 
v_unused_909_ = lean_ctor_get(v_r_694_, 4);
lean_dec(v_unused_909_);
v_unused_910_ = lean_ctor_get(v_r_694_, 3);
lean_dec(v_unused_910_);
v_unused_911_ = lean_ctor_get(v_r_694_, 2);
lean_dec(v_unused_911_);
v_unused_912_ = lean_ctor_get(v_r_694_, 1);
lean_dec(v_unused_912_);
v_unused_913_ = lean_ctor_get(v_r_694_, 0);
lean_dec(v_unused_913_);
v___x_872_ = v_r_694_;
v_isShared_873_ = v_isSharedCheck_908_;
goto v_resetjp_871_;
}
else
{
lean_dec(v_r_694_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_908_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___x_896_; lean_object* v___y_898_; 
v___x_874_ = lean_nat_add(v___x_700_, v_size_690_);
lean_dec(v_size_690_);
v___x_875_ = lean_nat_add(v___x_874_, v_size_850_);
lean_dec(v___x_874_);
v___x_896_ = lean_nat_add(v___x_700_, v_size_862_);
if (lean_obj_tag(v_l_866_) == 0)
{
lean_object* v_size_906_; 
v_size_906_ = lean_ctor_get(v_l_866_, 0);
lean_inc(v_size_906_);
v___y_898_ = v_size_906_;
goto v___jp_897_;
}
else
{
lean_object* v___x_907_; 
v___x_907_ = lean_unsigned_to_nat(0u);
v___y_898_ = v___x_907_;
goto v___jp_897_;
}
v___jp_876_:
{
lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_880_ = lean_nat_add(v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec(v___y_878_);
lean_inc_ref(v_tree_847_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 4, v_tree_847_);
lean_ctor_set(v___x_872_, 3, v_r_867_);
lean_ctor_set(v___x_872_, 2, v_v_849_);
lean_ctor_set(v___x_872_, 1, v_k_848_);
lean_ctor_set(v___x_872_, 0, v___x_880_);
v___x_882_ = v___x_872_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_k_848_);
lean_ctor_set(v_reuseFailAlloc_895_, 2, v_v_849_);
lean_ctor_set(v_reuseFailAlloc_895_, 3, v_r_867_);
lean_ctor_set(v_reuseFailAlloc_895_, 4, v_tree_847_);
v___x_882_ = v_reuseFailAlloc_895_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
v_isSharedCheck_889_ = !lean_is_exclusive(v_tree_847_);
if (v_isSharedCheck_889_ == 0)
{
lean_object* v_unused_890_; lean_object* v_unused_891_; lean_object* v_unused_892_; lean_object* v_unused_893_; lean_object* v_unused_894_; 
v_unused_890_ = lean_ctor_get(v_tree_847_, 4);
lean_dec(v_unused_890_);
v_unused_891_ = lean_ctor_get(v_tree_847_, 3);
lean_dec(v_unused_891_);
v_unused_892_ = lean_ctor_get(v_tree_847_, 2);
lean_dec(v_unused_892_);
v_unused_893_ = lean_ctor_get(v_tree_847_, 1);
lean_dec(v_unused_893_);
v_unused_894_ = lean_ctor_get(v_tree_847_, 0);
lean_dec(v_unused_894_);
v___x_884_ = v_tree_847_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_dec(v_tree_847_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 4, v___x_882_);
lean_ctor_set(v___x_884_, 3, v___y_877_);
lean_ctor_set(v___x_884_, 2, v_v_865_);
lean_ctor_set(v___x_884_, 1, v_k_864_);
lean_ctor_set(v___x_884_, 0, v___x_875_);
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_k_864_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v_v_865_);
lean_ctor_set(v_reuseFailAlloc_888_, 3, v___y_877_);
lean_ctor_set(v_reuseFailAlloc_888_, 4, v___x_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
v___jp_897_:
{
lean_object* v___x_899_; lean_object* v___x_901_; 
v___x_899_ = lean_nat_add(v___x_896_, v___y_898_);
lean_dec(v___y_898_);
lean_dec(v___x_896_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 4, v_l_866_);
lean_ctor_set(v___x_844_, 3, v_l_693_);
lean_ctor_set(v___x_844_, 2, v_v_692_);
lean_ctor_set(v___x_844_, 1, v_k_691_);
lean_ctor_set(v___x_844_, 0, v___x_899_);
v___x_901_ = v___x_844_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_899_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_k_691_);
lean_ctor_set(v_reuseFailAlloc_905_, 2, v_v_692_);
lean_ctor_set(v_reuseFailAlloc_905_, 3, v_l_693_);
lean_ctor_set(v_reuseFailAlloc_905_, 4, v_l_866_);
v___x_901_ = v_reuseFailAlloc_905_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
lean_object* v___x_902_; 
v___x_902_ = lean_nat_add(v___x_700_, v_size_850_);
if (lean_obj_tag(v_r_867_) == 0)
{
lean_object* v_size_903_; 
v_size_903_ = lean_ctor_get(v_r_867_, 0);
lean_inc(v_size_903_);
v___y_877_ = v___x_901_;
v___y_878_ = v___x_902_;
v___y_879_ = v_size_903_;
goto v___jp_876_;
}
else
{
lean_object* v___x_904_; 
v___x_904_ = lean_unsigned_to_nat(0u);
v___y_877_ = v___x_901_;
v___y_878_ = v___x_902_;
v___y_879_ = v___x_904_;
goto v___jp_876_;
}
}
}
}
}
else
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_914_ = lean_nat_add(v___x_700_, v_size_690_);
lean_dec(v_size_690_);
v___x_915_ = lean_nat_add(v___x_914_, v_size_850_);
lean_dec(v___x_914_);
v___x_916_ = lean_nat_add(v___x_700_, v_size_850_);
v___x_917_ = lean_nat_add(v___x_916_, v_size_863_);
lean_dec(v___x_916_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 4, v_tree_847_);
lean_ctor_set(v___x_844_, 3, v_r_694_);
lean_ctor_set(v___x_844_, 2, v_v_849_);
lean_ctor_set(v___x_844_, 1, v_k_848_);
lean_ctor_set(v___x_844_, 0, v___x_917_);
v___x_919_ = v___x_844_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_k_848_);
lean_ctor_set(v_reuseFailAlloc_923_, 2, v_v_849_);
lean_ctor_set(v_reuseFailAlloc_923_, 3, v_r_694_);
lean_ctor_set(v_reuseFailAlloc_923_, 4, v_tree_847_);
v___x_919_ = v_reuseFailAlloc_923_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
lean_object* v___x_921_; 
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 4, v___x_919_);
lean_ctor_set(v___x_860_, 0, v___x_915_);
v___x_921_ = v___x_860_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_922_, 1, v_k_691_);
lean_ctor_set(v_reuseFailAlloc_922_, 2, v_v_692_);
lean_ctor_set(v_reuseFailAlloc_922_, 3, v_l_693_);
lean_ctor_set(v_reuseFailAlloc_922_, 4, v___x_919_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_693_) == 0)
{
lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_953_; 
lean_inc_ref(v_l_693_);
lean_inc(v_v_692_);
lean_inc(v_k_691_);
lean_inc(v_size_690_);
v_isSharedCheck_953_ = !lean_is_exclusive(v_l_680_);
if (v_isSharedCheck_953_ == 0)
{
lean_object* v_unused_954_; lean_object* v_unused_955_; lean_object* v_unused_956_; lean_object* v_unused_957_; lean_object* v_unused_958_; 
v_unused_954_ = lean_ctor_get(v_l_680_, 4);
lean_dec(v_unused_954_);
v_unused_955_ = lean_ctor_get(v_l_680_, 3);
lean_dec(v_unused_955_);
v_unused_956_ = lean_ctor_get(v_l_680_, 2);
lean_dec(v_unused_956_);
v_unused_957_ = lean_ctor_get(v_l_680_, 1);
lean_dec(v_unused_957_);
v_unused_958_ = lean_ctor_get(v_l_680_, 0);
lean_dec(v_unused_958_);
v___x_931_ = v_l_680_;
v_isShared_932_ = v_isSharedCheck_953_;
goto v_resetjp_930_;
}
else
{
lean_dec(v_l_680_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_953_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
if (lean_obj_tag(v_r_694_) == 0)
{
lean_object* v_k_933_; lean_object* v_v_934_; lean_object* v_size_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_939_; 
v_k_933_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_k_933_);
v_v_934_ = lean_ctor_get(v___x_846_, 1);
lean_inc(v_v_934_);
lean_dec_ref(v___x_846_);
v_size_935_ = lean_ctor_get(v_r_694_, 0);
v___x_936_ = lean_nat_add(v___x_700_, v_size_690_);
lean_dec(v_size_690_);
v___x_937_ = lean_nat_add(v___x_700_, v_size_935_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 4, v_tree_847_);
lean_ctor_set(v___x_844_, 3, v_r_694_);
lean_ctor_set(v___x_844_, 2, v_v_934_);
lean_ctor_set(v___x_844_, 1, v_k_933_);
lean_ctor_set(v___x_844_, 0, v___x_937_);
v___x_939_ = v___x_844_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v_k_933_);
lean_ctor_set(v_reuseFailAlloc_943_, 2, v_v_934_);
lean_ctor_set(v_reuseFailAlloc_943_, 3, v_r_694_);
lean_ctor_set(v_reuseFailAlloc_943_, 4, v_tree_847_);
v___x_939_ = v_reuseFailAlloc_943_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_941_; 
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 4, v___x_939_);
lean_ctor_set(v___x_931_, 0, v___x_936_);
v___x_941_ = v___x_931_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_936_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v_k_691_);
lean_ctor_set(v_reuseFailAlloc_942_, 2, v_v_692_);
lean_ctor_set(v_reuseFailAlloc_942_, 3, v_l_693_);
lean_ctor_set(v_reuseFailAlloc_942_, 4, v___x_939_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
else
{
lean_object* v_k_944_; lean_object* v_v_945_; lean_object* v___x_946_; lean_object* v___x_948_; 
lean_dec(v_size_690_);
v_k_944_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_k_944_);
v_v_945_ = lean_ctor_get(v___x_846_, 1);
lean_inc(v_v_945_);
lean_dec_ref(v___x_846_);
v___x_946_ = lean_unsigned_to_nat(3u);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 4, v_r_694_);
lean_ctor_set(v___x_844_, 3, v_r_694_);
lean_ctor_set(v___x_844_, 2, v_v_945_);
lean_ctor_set(v___x_844_, 1, v_k_944_);
lean_ctor_set(v___x_844_, 0, v___x_700_);
v___x_948_ = v___x_844_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_k_944_);
lean_ctor_set(v_reuseFailAlloc_952_, 2, v_v_945_);
lean_ctor_set(v_reuseFailAlloc_952_, 3, v_r_694_);
lean_ctor_set(v_reuseFailAlloc_952_, 4, v_r_694_);
v___x_948_ = v_reuseFailAlloc_952_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_950_; 
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 4, v___x_948_);
lean_ctor_set(v___x_931_, 0, v___x_946_);
v___x_950_ = v___x_931_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_946_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v_k_691_);
lean_ctor_set(v_reuseFailAlloc_951_, 2, v_v_692_);
lean_ctor_set(v_reuseFailAlloc_951_, 3, v_l_693_);
lean_ctor_set(v_reuseFailAlloc_951_, 4, v___x_948_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_694_) == 0)
{
lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_983_; 
lean_inc(v_l_693_);
lean_inc(v_v_692_);
lean_inc(v_k_691_);
v_isSharedCheck_983_ = !lean_is_exclusive(v_l_680_);
if (v_isSharedCheck_983_ == 0)
{
lean_object* v_unused_984_; lean_object* v_unused_985_; lean_object* v_unused_986_; lean_object* v_unused_987_; lean_object* v_unused_988_; 
v_unused_984_ = lean_ctor_get(v_l_680_, 4);
lean_dec(v_unused_984_);
v_unused_985_ = lean_ctor_get(v_l_680_, 3);
lean_dec(v_unused_985_);
v_unused_986_ = lean_ctor_get(v_l_680_, 2);
lean_dec(v_unused_986_);
v_unused_987_ = lean_ctor_get(v_l_680_, 1);
lean_dec(v_unused_987_);
v_unused_988_ = lean_ctor_get(v_l_680_, 0);
lean_dec(v_unused_988_);
v___x_960_ = v_l_680_;
v_isShared_961_ = v_isSharedCheck_983_;
goto v_resetjp_959_;
}
else
{
lean_dec(v_l_680_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_983_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v_k_962_; lean_object* v_v_963_; lean_object* v_k_964_; lean_object* v_v_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_979_; 
v_k_962_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_k_962_);
v_v_963_ = lean_ctor_get(v___x_846_, 1);
lean_inc(v_v_963_);
lean_dec_ref(v___x_846_);
v_k_964_ = lean_ctor_get(v_r_694_, 1);
v_v_965_ = lean_ctor_get(v_r_694_, 2);
v_isSharedCheck_979_ = !lean_is_exclusive(v_r_694_);
if (v_isSharedCheck_979_ == 0)
{
lean_object* v_unused_980_; lean_object* v_unused_981_; lean_object* v_unused_982_; 
v_unused_980_ = lean_ctor_get(v_r_694_, 4);
lean_dec(v_unused_980_);
v_unused_981_ = lean_ctor_get(v_r_694_, 3);
lean_dec(v_unused_981_);
v_unused_982_ = lean_ctor_get(v_r_694_, 0);
lean_dec(v_unused_982_);
v___x_967_ = v_r_694_;
v_isShared_968_ = v_isSharedCheck_979_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_v_965_);
lean_inc(v_k_964_);
lean_dec(v_r_694_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_979_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_969_; lean_object* v___x_971_; 
v___x_969_ = lean_unsigned_to_nat(3u);
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 4, v_l_693_);
lean_ctor_set(v___x_967_, 3, v_l_693_);
lean_ctor_set(v___x_967_, 2, v_v_692_);
lean_ctor_set(v___x_967_, 1, v_k_691_);
lean_ctor_set(v___x_967_, 0, v___x_700_);
v___x_971_ = v___x_967_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_978_, 1, v_k_691_);
lean_ctor_set(v_reuseFailAlloc_978_, 2, v_v_692_);
lean_ctor_set(v_reuseFailAlloc_978_, 3, v_l_693_);
lean_ctor_set(v_reuseFailAlloc_978_, 4, v_l_693_);
v___x_971_ = v_reuseFailAlloc_978_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
lean_object* v___x_973_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 4, v_l_693_);
lean_ctor_set(v___x_844_, 3, v_l_693_);
lean_ctor_set(v___x_844_, 2, v_v_963_);
lean_ctor_set(v___x_844_, 1, v_k_962_);
lean_ctor_set(v___x_844_, 0, v___x_700_);
v___x_973_ = v___x_844_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_977_, 1, v_k_962_);
lean_ctor_set(v_reuseFailAlloc_977_, 2, v_v_963_);
lean_ctor_set(v_reuseFailAlloc_977_, 3, v_l_693_);
lean_ctor_set(v_reuseFailAlloc_977_, 4, v_l_693_);
v___x_973_ = v_reuseFailAlloc_977_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_975_; 
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 4, v___x_973_);
lean_ctor_set(v___x_960_, 3, v___x_971_);
lean_ctor_set(v___x_960_, 2, v_v_965_);
lean_ctor_set(v___x_960_, 1, v_k_964_);
lean_ctor_set(v___x_960_, 0, v___x_969_);
v___x_975_ = v___x_960_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_969_);
lean_ctor_set(v_reuseFailAlloc_976_, 1, v_k_964_);
lean_ctor_set(v_reuseFailAlloc_976_, 2, v_v_965_);
lean_ctor_set(v_reuseFailAlloc_976_, 3, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_976_, 4, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
}
}
else
{
lean_object* v_k_989_; lean_object* v_v_990_; lean_object* v___x_991_; lean_object* v___x_993_; 
v_k_989_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_k_989_);
v_v_990_ = lean_ctor_get(v___x_846_, 1);
lean_inc(v_v_990_);
lean_dec_ref(v___x_846_);
v___x_991_ = lean_unsigned_to_nat(2u);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 4, v_r_694_);
lean_ctor_set(v___x_844_, 3, v_l_680_);
lean_ctor_set(v___x_844_, 2, v_v_990_);
lean_ctor_set(v___x_844_, 1, v_k_989_);
lean_ctor_set(v___x_844_, 0, v___x_991_);
v___x_993_ = v___x_844_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_k_989_);
lean_ctor_set(v_reuseFailAlloc_994_, 2, v_v_990_);
lean_ctor_set(v_reuseFailAlloc_994_, 3, v_l_680_);
lean_ctor_set(v_reuseFailAlloc_994_, 4, v_r_694_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
}
}
}
else
{
return v_l_680_;
}
}
else
{
return v_r_681_;
}
}
else
{
lean_object* v_val_1001_; lean_object* v___x_1003_; 
v_val_1001_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_val_1001_);
lean_dec_ref_known(v___x_689_, 1);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 2, v_val_1001_);
lean_ctor_set(v___x_683_, 1, v_k_675_);
v___x_1003_ = v___x_683_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_size_677_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v_k_675_);
lean_ctor_set(v_reuseFailAlloc_1004_, 2, v_val_1001_);
lean_ctor_set(v_reuseFailAlloc_1004_, 3, v_l_680_);
lean_ctor_set(v_reuseFailAlloc_1004_, 4, v_r_681_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
default: 
{
lean_object* v_impl_1005_; lean_object* v___x_1006_; 
lean_del_object(v___x_683_);
lean_dec(v_size_677_);
v_impl_1005_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_674_, v_k_675_, v_r_681_);
v___x_1006_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_678_, v_v_679_, v_l_680_, v_impl_1005_);
return v___x_1006_;
}
}
}
}
else
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = lean_box(0);
v___x_1009_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_674_, v___x_1008_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_dec(v_k_675_);
return v_t_676_;
}
else
{
lean_object* v_val_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v_val_1010_ = lean_ctor_get(v___x_1009_, 0);
lean_inc(v_val_1010_);
lean_dec_ref_known(v___x_1009_, 1);
v___x_1011_ = lean_unsigned_to_nat(1u);
v___x_1012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v_k_675_);
lean_ctor_set(v___x_1012_, 2, v_val_1010_);
lean_ctor_set(v___x_1012_, 3, v_t_676_);
lean_ctor_set(v___x_1012_, 4, v_t_676_);
return v___x_1012_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1013_, lean_object* v_i_1014_, lean_object* v_k_1015_){
_start:
{
lean_object* v___x_1016_; uint8_t v___x_1017_; 
v___x_1016_ = lean_array_get_size(v_keys_1013_);
v___x_1017_ = lean_nat_dec_lt(v_i_1014_, v___x_1016_);
if (v___x_1017_ == 0)
{
lean_dec(v_i_1014_);
return v___x_1017_;
}
else
{
lean_object* v_k_x27_1018_; uint8_t v___x_1019_; 
v_k_x27_1018_ = lean_array_fget_borrowed(v_keys_1013_, v_i_1014_);
v___x_1019_ = lean_name_eq(v_k_1015_, v_k_x27_1018_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = lean_unsigned_to_nat(1u);
v___x_1021_ = lean_nat_add(v_i_1014_, v___x_1020_);
lean_dec(v_i_1014_);
v_i_1014_ = v___x_1021_;
goto _start;
}
else
{
lean_dec(v_i_1014_);
return v___x_1019_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1023_, lean_object* v_i_1024_, lean_object* v_k_1025_){
_start:
{
uint8_t v_res_1026_; lean_object* v_r_1027_; 
v_res_1026_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_1023_, v_i_1024_, v_k_1025_);
lean_dec(v_k_1025_);
lean_dec_ref(v_keys_1023_);
v_r_1027_ = lean_box(v_res_1026_);
return v_r_1027_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(lean_object* v_x_1028_, size_t v_x_1029_, lean_object* v_x_1030_){
_start:
{
if (lean_obj_tag(v_x_1028_) == 0)
{
lean_object* v_es_1031_; lean_object* v___x_1032_; size_t v___x_1033_; size_t v___x_1034_; lean_object* v_j_1035_; lean_object* v___x_1036_; 
v_es_1031_ = lean_ctor_get(v_x_1028_, 0);
v___x_1032_ = lean_box(2);
v___x_1033_ = ((size_t)31ULL);
v___x_1034_ = lean_usize_land(v_x_1029_, v___x_1033_);
v_j_1035_ = lean_usize_to_nat(v___x_1034_);
v___x_1036_ = lean_array_get_borrowed(v___x_1032_, v_es_1031_, v_j_1035_);
lean_dec(v_j_1035_);
switch(lean_obj_tag(v___x_1036_))
{
case 0:
{
lean_object* v_key_1037_; uint8_t v___x_1038_; 
v_key_1037_ = lean_ctor_get(v___x_1036_, 0);
v___x_1038_ = lean_name_eq(v_x_1030_, v_key_1037_);
return v___x_1038_;
}
case 1:
{
lean_object* v_node_1039_; size_t v___x_1040_; size_t v___x_1041_; 
v_node_1039_ = lean_ctor_get(v___x_1036_, 0);
v___x_1040_ = ((size_t)5ULL);
v___x_1041_ = lean_usize_shift_right(v_x_1029_, v___x_1040_);
v_x_1028_ = v_node_1039_;
v_x_1029_ = v___x_1041_;
goto _start;
}
default: 
{
uint8_t v___x_1043_; 
v___x_1043_ = 0;
return v___x_1043_;
}
}
}
else
{
lean_object* v_ks_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; 
v_ks_1044_ = lean_ctor_get(v_x_1028_, 0);
v___x_1045_ = lean_unsigned_to_nat(0u);
v___x_1046_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_ks_1044_, v___x_1045_, v_x_1030_);
return v___x_1046_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___boxed(lean_object* v_x_1047_, lean_object* v_x_1048_, lean_object* v_x_1049_){
_start:
{
size_t v_x_4158__boxed_1050_; uint8_t v_res_1051_; lean_object* v_r_1052_; 
v_x_4158__boxed_1050_ = lean_unbox_usize(v_x_1048_);
lean_dec(v_x_1048_);
v_res_1051_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1047_, v_x_4158__boxed_1050_, v_x_1049_);
lean_dec(v_x_1049_);
lean_dec_ref(v_x_1047_);
v_r_1052_ = lean_box(v_res_1051_);
return v_r_1052_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1053_; uint64_t v___x_1054_; 
v___x_1053_ = lean_unsigned_to_nat(1723u);
v___x_1054_ = lean_uint64_of_nat(v___x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(lean_object* v_x_1055_, lean_object* v_x_1056_){
_start:
{
uint64_t v___y_1058_; 
if (lean_obj_tag(v_x_1056_) == 0)
{
uint64_t v___x_1061_; 
v___x_1061_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0);
v___y_1058_ = v___x_1061_;
goto v___jp_1057_;
}
else
{
uint64_t v_hash_1062_; 
v_hash_1062_ = lean_ctor_get_uint64(v_x_1056_, sizeof(void*)*2);
v___y_1058_ = v_hash_1062_;
goto v___jp_1057_;
}
v___jp_1057_:
{
size_t v___x_1059_; uint8_t v___x_1060_; 
v___x_1059_ = lean_uint64_to_usize(v___y_1058_);
v___x_1060_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1055_, v___x_1059_, v_x_1056_);
return v___x_1060_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___boxed(lean_object* v_x_1063_, lean_object* v_x_1064_){
_start:
{
uint8_t v_res_1065_; lean_object* v_r_1066_; 
v_res_1065_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_1063_, v_x_1064_);
lean_dec(v_x_1064_);
lean_dec_ref(v_x_1063_);
v_r_1066_ = lean_box(v_res_1065_);
return v_r_1066_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(lean_object* v_tactics_1067_, lean_object* v_a_1068_, uint8_t v___x_1069_, lean_object* v_x_1070_, lean_object* v_____s_1071_){
_start:
{
lean_object* v_fst_1072_; lean_object* v_kinds_1073_; uint8_t v___x_1074_; 
v_fst_1072_ = lean_ctor_get(v_x_1070_, 0);
lean_inc(v_fst_1072_);
lean_dec_ref(v_x_1070_);
v_kinds_1073_ = lean_ctor_get(v_tactics_1067_, 1);
v___x_1074_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_kinds_1073_, v_fst_1072_);
if (v___x_1074_ == 0)
{
lean_object* v___x_1075_; 
lean_dec(v_fst_1072_);
lean_dec(v_a_1068_);
v___x_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1075_, 0, v_____s_1071_);
return v___x_1075_;
}
else
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1076_ = l_Lean_Name_toString(v_a_1068_, v___x_1069_);
v___x_1077_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_1076_, v_fst_1072_, v_____s_1071_);
v___x_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
return v___x_1078_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed(lean_object* v_tactics_1079_, lean_object* v_a_1080_, lean_object* v___x_1081_, lean_object* v_x_1082_, lean_object* v_____s_1083_){
_start:
{
uint8_t v___x_4220__boxed_1084_; lean_object* v_res_1085_; 
v___x_4220__boxed_1084_ = lean_unbox(v___x_1081_);
v_res_1085_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(v_tactics_1079_, v_a_1080_, v___x_4220__boxed_1084_, v_x_1082_, v_____s_1083_);
lean_dec_ref(v_tactics_1079_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(lean_object* v_f_1086_, lean_object* v_keys_1087_, lean_object* v_vals_1088_, lean_object* v_i_1089_, lean_object* v_acc_1090_){
_start:
{
lean_object* v___x_1091_; uint8_t v___x_1092_; 
v___x_1091_ = lean_array_get_size(v_keys_1087_);
v___x_1092_ = lean_nat_dec_lt(v_i_1089_, v___x_1091_);
if (v___x_1092_ == 0)
{
lean_object* v___x_1093_; 
lean_dec(v_i_1089_);
lean_dec_ref(v_f_1086_);
v___x_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1093_, 0, v_acc_1090_);
return v___x_1093_;
}
else
{
lean_object* v_k_1094_; lean_object* v_v_1095_; lean_object* v___x_1096_; 
v_k_1094_ = lean_array_fget_borrowed(v_keys_1087_, v_i_1089_);
v_v_1095_ = lean_array_fget_borrowed(v_vals_1088_, v_i_1089_);
lean_inc_ref(v_f_1086_);
lean_inc(v_v_1095_);
lean_inc(v_k_1094_);
v___x_1096_ = lean_apply_3(v_f_1086_, v_acc_1090_, v_k_1094_, v_v_1095_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_dec(v_i_1089_);
lean_dec_ref(v_f_1086_);
return v___x_1096_;
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_a_1097_);
lean_dec_ref_known(v___x_1096_, 1);
v___x_1098_ = lean_unsigned_to_nat(1u);
v___x_1099_ = lean_nat_add(v_i_1089_, v___x_1098_);
lean_dec(v_i_1089_);
v_i_1089_ = v___x_1099_;
v_acc_1090_ = v_a_1097_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_f_1101_, lean_object* v_keys_1102_, lean_object* v_vals_1103_, lean_object* v_i_1104_, lean_object* v_acc_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1101_, v_keys_1102_, v_vals_1103_, v_i_1104_, v_acc_1105_);
lean_dec_ref(v_vals_1103_);
lean_dec_ref(v_keys_1102_);
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(lean_object* v_f_1107_, lean_object* v_x_1108_, lean_object* v_x_1109_){
_start:
{
if (lean_obj_tag(v_x_1108_) == 0)
{
lean_object* v_es_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1130_; 
v_es_1110_ = lean_ctor_get(v_x_1108_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_x_1108_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1112_ = v_x_1108_;
v_isShared_1113_ = v_isSharedCheck_1130_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_es_1110_);
lean_dec(v_x_1108_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1130_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1114_ = lean_unsigned_to_nat(0u);
v___x_1115_ = lean_array_get_size(v_es_1110_);
v___x_1116_ = lean_nat_dec_lt(v___x_1114_, v___x_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1118_; 
lean_dec_ref(v_es_1110_);
lean_dec_ref(v_f_1107_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set_tag(v___x_1112_, 1);
lean_ctor_set(v___x_1112_, 0, v_x_1109_);
v___x_1118_ = v___x_1112_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_x_1109_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
else
{
uint8_t v___x_1120_; 
v___x_1120_ = lean_nat_dec_le(v___x_1115_, v___x_1115_);
if (v___x_1120_ == 0)
{
if (v___x_1116_ == 0)
{
lean_object* v___x_1122_; 
lean_dec_ref(v_es_1110_);
lean_dec_ref(v_f_1107_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set_tag(v___x_1112_, 1);
lean_ctor_set(v___x_1112_, 0, v_x_1109_);
v___x_1122_ = v___x_1112_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_x_1109_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
else
{
size_t v___x_1124_; size_t v___x_1125_; lean_object* v___x_1126_; 
lean_del_object(v___x_1112_);
v___x_1124_ = ((size_t)0ULL);
v___x_1125_ = lean_usize_of_nat(v___x_1115_);
v___x_1126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1107_, v_es_1110_, v___x_1124_, v___x_1125_, v_x_1109_);
lean_dec_ref(v_es_1110_);
return v___x_1126_;
}
}
else
{
size_t v___x_1127_; size_t v___x_1128_; lean_object* v___x_1129_; 
lean_del_object(v___x_1112_);
v___x_1127_ = ((size_t)0ULL);
v___x_1128_ = lean_usize_of_nat(v___x_1115_);
v___x_1129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1107_, v_es_1110_, v___x_1127_, v___x_1128_, v_x_1109_);
lean_dec_ref(v_es_1110_);
return v___x_1129_;
}
}
}
}
else
{
lean_object* v_ks_1131_; lean_object* v_vs_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v_ks_1131_ = lean_ctor_get(v_x_1108_, 0);
lean_inc_ref(v_ks_1131_);
v_vs_1132_ = lean_ctor_get(v_x_1108_, 1);
lean_inc_ref(v_vs_1132_);
lean_dec_ref_known(v_x_1108_, 2);
v___x_1133_ = lean_unsigned_to_nat(0u);
v___x_1134_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1107_, v_ks_1131_, v_vs_1132_, v___x_1133_, v_x_1109_);
lean_dec_ref(v_vs_1132_);
lean_dec_ref(v_ks_1131_);
return v___x_1134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(lean_object* v_f_1135_, lean_object* v_as_1136_, size_t v_i_1137_, size_t v_stop_1138_, lean_object* v_b_1139_){
_start:
{
lean_object* v_a_1141_; lean_object* v___y_1146_; uint8_t v___x_1148_; 
v___x_1148_ = lean_usize_dec_eq(v_i_1137_, v_stop_1138_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; 
v___x_1149_ = lean_array_uget_borrowed(v_as_1136_, v_i_1137_);
switch(lean_obj_tag(v___x_1149_))
{
case 0:
{
lean_object* v_key_1150_; lean_object* v_val_1151_; lean_object* v___x_1152_; 
v_key_1150_ = lean_ctor_get(v___x_1149_, 0);
v_val_1151_ = lean_ctor_get(v___x_1149_, 1);
lean_inc_ref(v_f_1135_);
lean_inc(v_val_1151_);
lean_inc(v_key_1150_);
v___x_1152_ = lean_apply_3(v_f_1135_, v_b_1139_, v_key_1150_, v_val_1151_);
v___y_1146_ = v___x_1152_;
goto v___jp_1145_;
}
case 1:
{
lean_object* v_node_1153_; lean_object* v___x_1154_; 
v_node_1153_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_node_1153_);
lean_inc_ref(v_f_1135_);
v___x_1154_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1135_, v_node_1153_, v_b_1139_);
v___y_1146_ = v___x_1154_;
goto v___jp_1145_;
}
default: 
{
v_a_1141_ = v_b_1139_;
goto v___jp_1140_;
}
}
}
else
{
lean_object* v___x_1155_; 
lean_dec_ref(v_f_1135_);
v___x_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1155_, 0, v_b_1139_);
return v___x_1155_;
}
v___jp_1140_:
{
size_t v___x_1142_; size_t v___x_1143_; 
v___x_1142_ = ((size_t)1ULL);
v___x_1143_ = lean_usize_add(v_i_1137_, v___x_1142_);
v_i_1137_ = v___x_1143_;
v_b_1139_ = v_a_1141_;
goto _start;
}
v___jp_1145_:
{
if (lean_obj_tag(v___y_1146_) == 0)
{
lean_dec_ref(v_f_1135_);
return v___y_1146_;
}
else
{
lean_object* v_a_1147_; 
v_a_1147_ = lean_ctor_get(v___y_1146_, 0);
lean_inc(v_a_1147_);
lean_dec_ref_known(v___y_1146_, 1);
v_a_1141_ = v_a_1147_;
goto v___jp_1140_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_f_1156_, lean_object* v_as_1157_, lean_object* v_i_1158_, lean_object* v_stop_1159_, lean_object* v_b_1160_){
_start:
{
size_t v_i_boxed_1161_; size_t v_stop_boxed_1162_; lean_object* v_res_1163_; 
v_i_boxed_1161_ = lean_unbox_usize(v_i_1158_);
lean_dec(v_i_1158_);
v_stop_boxed_1162_ = lean_unbox_usize(v_stop_1159_);
lean_dec(v_stop_1159_);
v_res_1163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1156_, v_as_1157_, v_i_boxed_1161_, v_stop_boxed_1162_, v_b_1160_);
lean_dec_ref(v_as_1157_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0(lean_object* v_f_1164_, lean_object* v_s_1165_, lean_object* v_a_1166_, lean_object* v_b_1167_){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1168_, 0, v_a_1166_);
lean_ctor_set(v___x_1168_, 1, v_b_1167_);
v___x_1169_ = lean_apply_2(v_f_1164_, v___x_1168_, v_s_1165_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1169_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1169_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
v_a_1178_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1169_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1169_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(lean_object* v_map_1186_, lean_object* v_init_1187_, lean_object* v_f_1188_){
_start:
{
lean_object* v___f_1189_; lean_object* v___x_1190_; lean_object* v_a_1191_; 
v___f_1189_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1189_, 0, v_f_1188_);
lean_inc_ref(v_map_1186_);
v___x_1190_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v___f_1189_, v_map_1186_, v_init_1187_);
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_a_1191_);
lean_dec_ref(v___x_1190_);
return v_a_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___boxed(lean_object* v_map_1192_, lean_object* v_init_1193_, lean_object* v_f_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_1192_, v_init_1193_, v_f_1194_);
lean_dec_ref(v_map_1192_);
return v_res_1195_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1196_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0);
v___x_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(lean_object* v_tactics_1199_, lean_object* v_a_1200_, uint8_t v___x_1201_, lean_object* v_as_x27_1202_, lean_object* v_b_1203_){
_start:
{
if (lean_obj_tag(v_as_x27_1202_) == 0)
{
lean_dec(v_a_1200_);
lean_dec_ref(v_tactics_1199_);
return v_b_1203_;
}
else
{
lean_object* v_head_1204_; lean_object* v_fst_1205_; lean_object* v_info_1206_; lean_object* v_tail_1207_; lean_object* v_collectKinds_1208_; lean_object* v___x_1209_; lean_object* v___f_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v_head_1204_ = lean_ctor_get(v_as_x27_1202_, 0);
v_fst_1205_ = lean_ctor_get(v_head_1204_, 0);
v_info_1206_ = lean_ctor_get(v_fst_1205_, 0);
v_tail_1207_ = lean_ctor_get(v_as_x27_1202_, 1);
v_collectKinds_1208_ = lean_ctor_get(v_info_1206_, 1);
v___x_1209_ = lean_box(v___x_1201_);
lean_inc(v_a_1200_);
lean_inc_ref(v_tactics_1199_);
v___f_1210_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1210_, 0, v_tactics_1199_);
lean_closure_set(v___f_1210_, 1, v_a_1200_);
lean_closure_set(v___f_1210_, 2, v___x_1209_);
v___x_1211_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1);
lean_inc_ref(v_collectKinds_1208_);
v___x_1212_ = lean_apply_1(v_collectKinds_1208_, v___x_1211_);
v___x_1213_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v___x_1212_, v_b_1203_, v___f_1210_);
lean_dec_ref(v___x_1212_);
v_as_x27_1202_ = v_tail_1207_;
v_b_1203_ = v___x_1213_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___boxed(lean_object* v_tactics_1215_, lean_object* v_a_1216_, lean_object* v___x_1217_, lean_object* v_as_x27_1218_, lean_object* v_b_1219_){
_start:
{
uint8_t v___x_4394__boxed_1220_; lean_object* v_res_1221_; 
v___x_4394__boxed_1220_ = lean_unbox(v___x_1217_);
v_res_1221_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1215_, v_a_1216_, v___x_4394__boxed_1220_, v_as_x27_1218_, v_b_1219_);
lean_dec(v_as_x27_1218_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(lean_object* v_tactics_1225_, lean_object* v_init_1226_, lean_object* v_x_1227_){
_start:
{
if (lean_obj_tag(v_x_1227_) == 0)
{
lean_object* v_k_1228_; lean_object* v_v_1229_; lean_object* v_l_1230_; lean_object* v_r_1231_; lean_object* v___x_1232_; lean_object* v_a_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; 
v_k_1228_ = lean_ctor_get(v_x_1227_, 1);
lean_inc(v_k_1228_);
v_v_1229_ = lean_ctor_get(v_x_1227_, 2);
lean_inc(v_v_1229_);
v_l_1230_ = lean_ctor_get(v_x_1227_, 3);
lean_inc(v_l_1230_);
v_r_1231_ = lean_ctor_get(v_x_1227_, 4);
lean_inc(v_r_1231_);
lean_dec_ref_known(v_x_1227_, 5);
lean_inc_ref(v_tactics_1225_);
v___x_1232_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_1225_, v_init_1226_, v_l_1230_);
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1233_);
v___x_1234_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__1));
v___x_1235_ = lean_name_eq(v_k_1228_, v___x_1234_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; 
lean_dec_ref(v___x_1232_);
lean_inc_ref(v_tactics_1225_);
v___x_1236_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1225_, v_k_1228_, v___x_1235_, v_v_1229_, v_a_1233_);
lean_dec(v_v_1229_);
v_init_1226_ = v___x_1236_;
v_x_1227_ = v_r_1231_;
goto _start;
}
else
{
lean_object* v_a_1238_; 
lean_dec(v_a_1233_);
lean_dec(v_v_1229_);
lean_dec(v_k_1228_);
v_a_1238_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1238_);
lean_dec_ref(v___x_1232_);
v_init_1226_ = v_a_1238_;
v_x_1227_ = v_r_1231_;
goto _start;
}
}
else
{
lean_object* v___x_1240_; 
lean_dec_ref(v_tactics_1225_);
v___x_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1240_, 0, v_init_1226_);
return v___x_1240_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(lean_object* v_tactics_1241_, lean_object* v_table_1242_, lean_object* v_firsts_1243_){
_start:
{
lean_object* v___x_1244_; lean_object* v_a_1245_; 
v___x_1244_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_1241_, v_firsts_1243_, v_table_1242_);
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1245_);
lean_dec_ref(v___x_1244_);
return v_a_1245_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(lean_object* v_00_u03b2_1246_, lean_object* v_x_1247_, lean_object* v_x_1248_){
_start:
{
uint8_t v___x_1249_; 
v___x_1249_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_1247_, v_x_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___boxed(lean_object* v_00_u03b2_1250_, lean_object* v_x_1251_, lean_object* v_x_1252_){
_start:
{
uint8_t v_res_1253_; lean_object* v_r_1254_; 
v_res_1253_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(v_00_u03b2_1250_, v_x_1251_, v_x_1252_);
lean_dec(v_x_1252_);
lean_dec_ref(v_x_1251_);
v_r_1254_ = lean_box(v_res_1253_);
return v_r_1254_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1(lean_object* v___x_1255_, lean_object* v_k_1256_, lean_object* v_t_1257_, lean_object* v_hl_1258_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_1255_, v_k_1256_, v_t_1257_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(lean_object* v_00_u03c3_1260_, lean_object* v_00_u03b2_1261_, lean_object* v_map_1262_, lean_object* v_init_1263_, lean_object* v_f_1264_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_1262_, v_init_1263_, v_f_1264_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___boxed(lean_object* v_00_u03c3_1266_, lean_object* v_00_u03b2_1267_, lean_object* v_map_1268_, lean_object* v_init_1269_, lean_object* v_f_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(v_00_u03c3_1266_, v_00_u03b2_1267_, v_map_1268_, v_init_1269_, v_f_1270_);
lean_dec_ref(v_map_1268_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(lean_object* v_tactics_1272_, lean_object* v_a_1273_, uint8_t v___x_1274_, lean_object* v_as_1275_, lean_object* v_as_x27_1276_, lean_object* v_b_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1272_, v_a_1273_, v___x_1274_, v_as_x27_1276_, v_b_1277_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___boxed(lean_object* v_tactics_1280_, lean_object* v_a_1281_, lean_object* v___x_1282_, lean_object* v_as_1283_, lean_object* v_as_x27_1284_, lean_object* v_b_1285_, lean_object* v_a_1286_){
_start:
{
uint8_t v___x_4477__boxed_1287_; lean_object* v_res_1288_; 
v___x_4477__boxed_1287_ = lean_unbox(v___x_1282_);
v_res_1288_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(v_tactics_1280_, v_a_1281_, v___x_4477__boxed_1287_, v_as_1283_, v_as_x27_1284_, v_b_1285_, v_a_1286_);
lean_dec(v_as_x27_1284_);
lean_dec(v_as_1283_);
return v_res_1288_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(lean_object* v_00_u03b2_1289_, lean_object* v_x_1290_, size_t v_x_1291_, lean_object* v_x_1292_){
_start:
{
uint8_t v___x_1293_; 
v___x_1293_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1290_, v_x_1291_, v_x_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1294_, lean_object* v_x_1295_, lean_object* v_x_1296_, lean_object* v_x_1297_){
_start:
{
size_t v_x_4486__boxed_1298_; uint8_t v_res_1299_; lean_object* v_r_1300_; 
v_x_4486__boxed_1298_ = lean_unbox_usize(v_x_1296_);
lean_dec(v_x_1296_);
v_res_1299_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(v_00_u03b2_1294_, v_x_1295_, v_x_4486__boxed_1298_, v_x_1297_);
lean_dec(v_x_1297_);
lean_dec_ref(v_x_1295_);
v_r_1300_ = lean_box(v_res_1299_);
return v_r_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3___redArg(lean_object* v_map_1301_, lean_object* v_f_1302_, lean_object* v_init_1303_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1302_, v_map_1301_, v_init_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3(lean_object* v_00_u03c3_1305_, lean_object* v_00_u03c3_1306_, lean_object* v_00_u03b2_1307_, lean_object* v_map_1308_, lean_object* v_f_1309_, lean_object* v_init_1310_){
_start:
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1309_, v_map_1308_, v_init_1310_);
return v___x_1311_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1312_, lean_object* v_keys_1313_, lean_object* v_vals_1314_, lean_object* v_heq_1315_, lean_object* v_i_1316_, lean_object* v_k_1317_){
_start:
{
uint8_t v___x_1318_; 
v___x_1318_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_1313_, v_i_1316_, v_k_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1319_, lean_object* v_keys_1320_, lean_object* v_vals_1321_, lean_object* v_heq_1322_, lean_object* v_i_1323_, lean_object* v_k_1324_){
_start:
{
uint8_t v_res_1325_; lean_object* v_r_1326_; 
v_res_1325_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(v_00_u03b2_1319_, v_keys_1320_, v_vals_1321_, v_heq_1322_, v_i_1323_, v_k_1324_);
lean_dec(v_k_1324_);
lean_dec_ref(v_vals_1321_);
lean_dec_ref(v_keys_1320_);
v_r_1326_ = lean_box(v_res_1325_);
return v_r_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5(lean_object* v_00_u03c3_1327_, lean_object* v_00_u03c3_1328_, lean_object* v_00_u03b1_1329_, lean_object* v_00_u03b2_1330_, lean_object* v_f_1331_, lean_object* v_x_1332_, lean_object* v_x_1333_){
_start:
{
lean_object* v___x_1334_; 
v___x_1334_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1331_, v_x_1332_, v_x_1333_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(lean_object* v_00_u03b1_1335_, lean_object* v_00_u03b2_1336_, lean_object* v_00_u03c3_1337_, lean_object* v_00_u03c3_1338_, lean_object* v_f_1339_, lean_object* v_as_1340_, size_t v_i_1341_, size_t v_stop_1342_, lean_object* v_b_1343_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1339_, v_as_1340_, v_i_1341_, v_stop_1342_, v_b_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1345_, lean_object* v_00_u03b2_1346_, lean_object* v_00_u03c3_1347_, lean_object* v_00_u03c3_1348_, lean_object* v_f_1349_, lean_object* v_as_1350_, lean_object* v_i_1351_, lean_object* v_stop_1352_, lean_object* v_b_1353_){
_start:
{
size_t v_i_boxed_1354_; size_t v_stop_boxed_1355_; lean_object* v_res_1356_; 
v_i_boxed_1354_ = lean_unbox_usize(v_i_1351_);
lean_dec(v_i_1351_);
v_stop_boxed_1355_ = lean_unbox_usize(v_stop_1352_);
lean_dec(v_stop_1352_);
v_res_1356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(v_00_u03b1_1345_, v_00_u03b2_1346_, v_00_u03c3_1347_, v_00_u03c3_1348_, v_f_1349_, v_as_1350_, v_i_boxed_1354_, v_stop_boxed_1355_, v_b_1353_);
lean_dec_ref(v_as_1350_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(lean_object* v_00_u03c3_1357_, lean_object* v_00_u03c3_1358_, lean_object* v_00_u03b1_1359_, lean_object* v_00_u03b2_1360_, lean_object* v_f_1361_, lean_object* v_keys_1362_, lean_object* v_vals_1363_, lean_object* v_heq_1364_, lean_object* v_i_1365_, lean_object* v_acc_1366_){
_start:
{
lean_object* v___x_1367_; 
v___x_1367_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1361_, v_keys_1362_, v_vals_1363_, v_i_1365_, v_acc_1366_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03c3_1368_, lean_object* v_00_u03c3_1369_, lean_object* v_00_u03b1_1370_, lean_object* v_00_u03b2_1371_, lean_object* v_f_1372_, lean_object* v_keys_1373_, lean_object* v_vals_1374_, lean_object* v_heq_1375_, lean_object* v_i_1376_, lean_object* v_acc_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(v_00_u03c3_1368_, v_00_u03c3_1369_, v_00_u03b1_1370_, v_00_u03b2_1371_, v_f_1372_, v_keys_1373_, v_vals_1374_, v_heq_1375_, v_i_1376_, v_acc_1377_);
lean_dec_ref(v_vals_1374_);
lean_dec_ref(v_keys_1373_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0(lean_object* v_x1_1379_, lean_object* v_x2_1380_){
_start:
{
lean_object* v_fst_1381_; lean_object* v_snd_1382_; lean_object* v___x_1383_; 
v_fst_1381_ = lean_ctor_get(v_x2_1380_, 0);
lean_inc(v_fst_1381_);
v_snd_1382_ = lean_ctor_get(v_x2_1380_, 1);
lean_inc(v_snd_1382_);
lean_dec_ref(v_x2_1380_);
v___x_1383_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_1381_, v_snd_1382_, v_x1_1379_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1(lean_object* v___f_1403_, lean_object* v_x1_1404_, lean_object* v_x2_1405_){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; uint8_t v___x_1409_; 
v___x_1406_ = lean_unsigned_to_nat(0u);
v___x_1407_ = lean_array_get_size(v_x2_1405_);
v___x_1408_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_1409_ = lean_nat_dec_lt(v___x_1406_, v___x_1407_);
if (v___x_1409_ == 0)
{
lean_dec_ref(v_x2_1405_);
lean_dec_ref(v___f_1403_);
return v_x1_1404_;
}
else
{
uint8_t v___x_1410_; 
v___x_1410_ = lean_nat_dec_le(v___x_1407_, v___x_1407_);
if (v___x_1410_ == 0)
{
if (v___x_1409_ == 0)
{
lean_dec_ref(v_x2_1405_);
lean_dec_ref(v___f_1403_);
return v_x1_1404_;
}
else
{
size_t v___x_1411_; size_t v___x_1412_; lean_object* v___x_1413_; 
v___x_1411_ = ((size_t)0ULL);
v___x_1412_ = lean_usize_of_nat(v___x_1407_);
v___x_1413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1408_, v___f_1403_, v_x2_1405_, v___x_1411_, v___x_1412_, v_x1_1404_);
return v___x_1413_;
}
}
else
{
size_t v___x_1414_; size_t v___x_1415_; lean_object* v___x_1416_; 
v___x_1414_ = ((size_t)0ULL);
v___x_1415_ = lean_usize_of_nat(v___x_1407_);
v___x_1416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1408_, v___f_1403_, v_x2_1405_, v___x_1414_, v___x_1415_, v_x1_1404_);
return v___x_1416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(lean_object* v___x_1420_, lean_object* v___x_1421_, lean_object* v___x_1422_, lean_object* v___x_1423_, lean_object* v___x_1424_, lean_object* v_toPure_1425_, lean_object* v___f_1426_, lean_object* v_env_1427_){
_start:
{
lean_object* v___x_1428_; lean_object* v_ext_1429_; lean_object* v_toEnvExtension_1430_; lean_object* v_asyncMode_1431_; lean_object* v___x_1432_; lean_object* v_categories_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1428_ = l_Lean_Parser_parserExtension;
v_ext_1429_ = lean_ctor_get(v___x_1428_, 1);
v_toEnvExtension_1430_ = lean_ctor_get(v_ext_1429_, 0);
v_asyncMode_1431_ = lean_ctor_get(v_toEnvExtension_1430_, 2);
lean_inc_ref(v_env_1427_);
v___x_1432_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1420_, v___x_1428_, v_env_1427_, v_asyncMode_1431_);
v_categories_1433_ = lean_ctor_get(v___x_1432_, 2);
lean_inc_ref(v_categories_1433_);
lean_dec(v___x_1432_);
v___x_1434_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_1435_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_1421_, v___x_1422_, v_categories_1433_, v___x_1434_);
lean_dec_ref(v_categories_1433_);
if (lean_obj_tag(v___x_1435_) == 1)
{
lean_object* v_val_1436_; lean_object* v___y_1438_; lean_object* v___x_1445_; lean_object* v_toEnvExtension_1446_; lean_object* v_exportEntriesFn_1447_; lean_object* v_asyncMode_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v_importedEntries_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v_exported_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; uint8_t v___x_1460_; 
v_val_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_val_1436_);
lean_dec_ref_known(v___x_1435_, 1);
v___x_1445_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_1446_ = lean_ctor_get(v___x_1445_, 0);
v_exportEntriesFn_1447_ = lean_ctor_get(v___x_1445_, 4);
v_asyncMode_1448_ = lean_ctor_get(v_toEnvExtension_1446_, 2);
v___x_1449_ = lean_box(0);
lean_inc_ref_n(v_env_1427_, 2);
v___x_1450_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1423_, v_toEnvExtension_1446_, v_env_1427_, v_asyncMode_1448_, v___x_1449_);
v_importedEntries_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc_ref(v_importedEntries_1451_);
lean_dec(v___x_1450_);
v___x_1452_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1424_, v___x_1445_, v_env_1427_, v_asyncMode_1448_, v___x_1449_);
lean_inc_ref(v_exportEntriesFn_1447_);
v___x_1453_ = lean_apply_2(v_exportEntriesFn_1447_, v_env_1427_, v___x_1452_);
v_exported_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_exported_1454_);
lean_dec_ref(v___x_1453_);
v___x_1455_ = lean_box(1);
v___x_1456_ = lean_array_push(v_importedEntries_1451_, v_exported_1454_);
v___x_1457_ = lean_unsigned_to_nat(0u);
v___x_1458_ = lean_array_get_size(v___x_1456_);
v___x_1459_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_1460_ = lean_nat_dec_lt(v___x_1457_, v___x_1458_);
if (v___x_1460_ == 0)
{
lean_dec_ref(v___x_1456_);
lean_dec_ref(v___f_1426_);
v___y_1438_ = v___x_1455_;
goto v___jp_1437_;
}
else
{
uint8_t v___x_1461_; 
v___x_1461_ = lean_nat_dec_le(v___x_1458_, v___x_1458_);
if (v___x_1461_ == 0)
{
if (v___x_1460_ == 0)
{
lean_dec_ref(v___x_1456_);
lean_dec_ref(v___f_1426_);
v___y_1438_ = v___x_1455_;
goto v___jp_1437_;
}
else
{
size_t v___x_1462_; size_t v___x_1463_; lean_object* v___x_1464_; 
v___x_1462_ = ((size_t)0ULL);
v___x_1463_ = lean_usize_of_nat(v___x_1458_);
v___x_1464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1459_, v___f_1426_, v___x_1456_, v___x_1462_, v___x_1463_, v___x_1455_);
v___y_1438_ = v___x_1464_;
goto v___jp_1437_;
}
}
else
{
size_t v___x_1465_; size_t v___x_1466_; lean_object* v___x_1467_; 
v___x_1465_ = ((size_t)0ULL);
v___x_1466_ = lean_usize_of_nat(v___x_1458_);
v___x_1467_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1459_, v___f_1426_, v___x_1456_, v___x_1465_, v___x_1466_, v___x_1455_);
v___y_1438_ = v___x_1467_;
goto v___jp_1437_;
}
}
v___jp_1437_:
{
lean_object* v_tables_1439_; lean_object* v_leadingTable_1440_; lean_object* v_trailingTable_1441_; lean_object* v_firstTokens_1442_; lean_object* v_firstTokens_1443_; lean_object* v___x_1444_; 
v_tables_1439_ = lean_ctor_get(v_val_1436_, 2);
v_leadingTable_1440_ = lean_ctor_get(v_tables_1439_, 0);
v_trailingTable_1441_ = lean_ctor_get(v_tables_1439_, 2);
lean_inc(v_trailingTable_1441_);
lean_inc(v_leadingTable_1440_);
lean_inc(v_val_1436_);
v_firstTokens_1442_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_1436_, v_leadingTable_1440_, v___y_1438_);
v_firstTokens_1443_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_1436_, v_trailingTable_1441_, v_firstTokens_1442_);
v___x_1444_ = lean_apply_2(v_toPure_1425_, lean_box(0), v_firstTokens_1443_);
return v___x_1444_;
}
}
else
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
lean_dec(v___x_1435_);
lean_dec_ref(v_env_1427_);
lean_dec_ref(v___f_1426_);
lean_dec(v___x_1424_);
v___x_1468_ = lean_box(1);
v___x_1469_ = lean_apply_2(v_toPure_1425_, lean_box(0), v___x_1468_);
return v___x_1469_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed(lean_object* v___x_1470_, lean_object* v___x_1471_, lean_object* v___x_1472_, lean_object* v___x_1473_, lean_object* v___x_1474_, lean_object* v_toPure_1475_, lean_object* v___f_1476_, lean_object* v_env_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(v___x_1470_, v___x_1471_, v___x_1472_, v___x_1473_, v___x_1474_, v_toPure_1475_, v___f_1476_, v_env_1477_);
lean_dec_ref(v___x_1473_);
lean_dec_ref(v___x_1470_);
return v_res_1478_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2(void){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = lean_box(1);
v___x_1483_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_1482_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(lean_object* v_inst_1486_, lean_object* v_inst_1487_){
_start:
{
lean_object* v_toApplicative_1488_; lean_object* v_toBind_1489_; lean_object* v_getEnv_1490_; lean_object* v_toPure_1491_; lean_object* v___f_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___f_1498_; lean_object* v___x_1499_; 
v_toApplicative_1488_ = lean_ctor_get(v_inst_1486_, 0);
lean_inc_ref(v_toApplicative_1488_);
v_toBind_1489_ = lean_ctor_get(v_inst_1486_, 1);
lean_inc(v_toBind_1489_);
lean_dec_ref(v_inst_1486_);
v_getEnv_1490_ = lean_ctor_get(v_inst_1487_, 0);
lean_inc(v_getEnv_1490_);
lean_dec_ref(v_inst_1487_);
v_toPure_1491_ = lean_ctor_get(v_toApplicative_1488_, 1);
lean_inc(v_toPure_1491_);
lean_dec_ref(v_toApplicative_1488_);
v___f_1492_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1));
v___x_1493_ = lean_box(1);
v___x_1494_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_1495_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_1496_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___x_1497_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___f_1498_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1498_, 0, v___x_1497_);
lean_closure_set(v___f_1498_, 1, v___x_1495_);
lean_closure_set(v___f_1498_, 2, v___x_1496_);
lean_closure_set(v___f_1498_, 3, v___x_1494_);
lean_closure_set(v___f_1498_, 4, v___x_1493_);
lean_closure_set(v___f_1498_, 5, v_toPure_1491_);
lean_closure_set(v___f_1498_, 6, v___f_1492_);
v___x_1499_ = lean_apply_4(v_toBind_1489_, lean_box(0), lean_box(0), v_getEnv_1490_, v___f_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens(lean_object* v_m_1500_, lean_object* v_inst_1501_, lean_object* v_inst_1502_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(v_inst_1501_, v_inst_1502_);
return v___x_1503_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1504_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__0);
v___x_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
return v___x_1506_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1507_ = lean_box(1);
v___x_1508_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg___closed__4);
v___x_1509_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__1);
v___x_1510_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
lean_ctor_set(v___x_1510_, 1, v___x_1508_);
lean_ctor_set(v___x_1510_, 2, v___x_1507_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(lean_object* v_n_1512_, lean_object* v___y_1513_, lean_object* v_toPure_1514_, lean_object* v_firsts_1515_, lean_object* v_____do__lift_1516_){
_start:
{
lean_object* v___y_1518_; lean_object* v_val_1529_; 
if (lean_obj_tag(v_____do__lift_1516_) == 0)
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__3));
lean_inc(v_n_1512_);
v___x_1532_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___x_1531_, v_firsts_1515_, v_n_1512_);
if (lean_obj_tag(v___x_1532_) == 0)
{
uint8_t v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1533_ = 1;
lean_inc(v_n_1512_);
v___x_1534_ = l_Lean_Name_toString(v_n_1512_, v___x_1533_);
v___x_1535_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
v___y_1518_ = v___x_1535_;
goto v___jp_1517_;
}
else
{
lean_object* v_val_1536_; 
v_val_1536_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_val_1536_);
lean_dec_ref_known(v___x_1532_, 1);
v_val_1529_ = v_val_1536_;
goto v___jp_1528_;
}
}
else
{
lean_object* v_val_1537_; 
lean_dec(v_firsts_1515_);
v_val_1537_ = lean_ctor_get(v_____do__lift_1516_, 0);
lean_inc(v_val_1537_);
lean_dec_ref_known(v_____do__lift_1516_, 1);
v_val_1529_ = v_val_1537_;
goto v___jp_1528_;
}
v___jp_1517_:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1519_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
v___x_1520_ = l_Lean_Expr_const___override(v_n_1512_, v___y_1513_);
v___x_1521_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2);
v___x_1522_ = lean_box(0);
v___x_1523_ = 0;
v___x_1524_ = l_Lean_MessageData_withExprHover(v___y_1518_, v___x_1520_, v___x_1521_, v___x_1522_, v___x_1522_, v___x_1522_, v___x_1523_);
v___x_1525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1519_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
v___x_1526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
lean_ctor_set(v___x_1526_, 1, v___x_1519_);
v___x_1527_ = lean_apply_2(v_toPure_1514_, lean_box(0), v___x_1526_);
return v___x_1527_;
}
v___jp_1528_:
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1530_, 0, v_val_1529_);
v___y_1518_ = v___x_1530_;
goto v___jp_1517_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1(lean_object* v_n_1538_, lean_object* v_toPure_1539_, lean_object* v_firsts_1540_, lean_object* v_inst_1541_, lean_object* v_inst_1542_, lean_object* v_toBind_1543_, lean_object* v___x_1544_, lean_object* v___x_1545_, lean_object* v___f_1546_, lean_object* v_env_1547_){
_start:
{
lean_object* v___y_1549_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = l_Lean_Environment_constants(v_env_1547_);
lean_inc(v_n_1538_);
v___x_1554_ = l_Lean_SMap_find_x3f_x27___redArg(v___x_1544_, v___x_1545_, v___x_1553_, v_n_1538_);
lean_dec_ref(v___x_1553_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v___x_1555_; 
lean_dec_ref(v___f_1546_);
v___x_1555_ = lean_box(0);
v___y_1549_ = v___x_1555_;
goto v___jp_1548_;
}
else
{
lean_object* v_val_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v_val_1556_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_val_1556_);
lean_dec_ref_known(v___x_1554_, 1);
v___x_1557_ = l_Lean_ConstantInfo_levelParams(v_val_1556_);
lean_dec(v_val_1556_);
v___x_1558_ = lean_box(0);
v___x_1559_ = l_List_mapTR_loop___redArg(v___f_1546_, v___x_1557_, v___x_1558_);
v___y_1549_ = v___x_1559_;
goto v___jp_1548_;
}
v___jp_1548_:
{
lean_object* v___f_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
lean_inc(v_n_1538_);
v___f_1550_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1550_, 0, v_n_1538_);
lean_closure_set(v___f_1550_, 1, v___y_1549_);
lean_closure_set(v___f_1550_, 2, v_toPure_1539_);
lean_closure_set(v___f_1550_, 3, v_firsts_1540_);
v___x_1551_ = l_Lean_Parser_Tactic_Doc_customTacticName___redArg(v_inst_1541_, v_inst_1542_, v_n_1538_);
v___x_1552_ = lean_apply_4(v_toBind_1543_, lean_box(0), lean_box(0), v___x_1551_, v___f_1550_);
return v___x_1552_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(lean_object* v_inst_1561_, lean_object* v_inst_1562_, lean_object* v_firsts_1563_, lean_object* v_n_1564_){
_start:
{
lean_object* v_toApplicative_1565_; lean_object* v_toBind_1566_; lean_object* v_getEnv_1567_; lean_object* v_toPure_1568_; lean_object* v___f_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___f_1572_; lean_object* v___x_1573_; 
v_toApplicative_1565_ = lean_ctor_get(v_inst_1561_, 0);
v_toBind_1566_ = lean_ctor_get(v_inst_1561_, 1);
lean_inc_n(v_toBind_1566_, 2);
v_getEnv_1567_ = lean_ctor_get(v_inst_1562_, 0);
lean_inc(v_getEnv_1567_);
v_toPure_1568_ = lean_ctor_get(v_toApplicative_1565_, 1);
lean_inc(v_toPure_1568_);
v___f_1569_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0));
v___x_1570_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_1571_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___f_1572_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1), 10, 9);
lean_closure_set(v___f_1572_, 0, v_n_1564_);
lean_closure_set(v___f_1572_, 1, v_toPure_1568_);
lean_closure_set(v___f_1572_, 2, v_firsts_1563_);
lean_closure_set(v___f_1572_, 3, v_inst_1561_);
lean_closure_set(v___f_1572_, 4, v_inst_1562_);
lean_closure_set(v___f_1572_, 5, v_toBind_1566_);
lean_closure_set(v___f_1572_, 6, v___x_1570_);
lean_closure_set(v___f_1572_, 7, v___x_1571_);
lean_closure_set(v___f_1572_, 8, v___f_1569_);
v___x_1573_ = lean_apply_4(v_toBind_1566_, lean_box(0), lean_box(0), v_getEnv_1567_, v___f_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName(lean_object* v_m_1574_, lean_object* v_inst_1575_, lean_object* v_inst_1576_, lean_object* v_firsts_1577_, lean_object* v_n_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(v_inst_1575_, v_inst_1576_, v_firsts_1577_, v_n_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(lean_object* v_s_1582_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0));
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___boxed(lean_object* v_s_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v_s_1584_);
lean_dec_ref(v_s_1584_);
return v_res_1585_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(uint8_t v___x_1586_, lean_object* v_x1_1587_, lean_object* v_x2_1588_){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; uint8_t v___x_1591_; 
v___x_1589_ = l_Lean_Name_toString(v_x1_1587_, v___x_1586_);
v___x_1590_ = l_Lean_Name_toString(v_x2_1588_, v___x_1586_);
v___x_1591_ = lean_string_dec_lt(v___x_1589_, v___x_1590_);
lean_dec_ref(v___x_1590_);
lean_dec_ref(v___x_1589_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0___boxed(lean_object* v___x_1592_, lean_object* v_x1_1593_, lean_object* v_x2_1594_){
_start:
{
uint8_t v___x_17020__boxed_1595_; uint8_t v_res_1596_; lean_object* v_r_1597_; 
v___x_17020__boxed_1595_ = lean_unbox(v___x_1592_);
v_res_1596_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_17020__boxed_1595_, v_x1_1593_, v_x2_1594_);
v_r_1597_ = lean_box(v_res_1596_);
return v_r_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(lean_object* v_hi_1598_, lean_object* v_pivot_1599_, lean_object* v_as_1600_, lean_object* v_i_1601_, lean_object* v_k_1602_){
_start:
{
uint8_t v___x_1603_; 
v___x_1603_ = lean_nat_dec_lt(v_k_1602_, v_hi_1598_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
lean_dec(v_k_1602_);
lean_dec(v_pivot_1599_);
v___x_1604_ = lean_array_fswap(v_as_1600_, v_i_1601_, v_hi_1598_);
v___x_1605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1605_, 0, v_i_1601_);
lean_ctor_set(v___x_1605_, 1, v___x_1604_);
return v___x_1605_;
}
else
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; uint8_t v___x_1609_; 
v___x_1606_ = lean_array_fget_borrowed(v_as_1600_, v_k_1602_);
lean_inc(v___x_1606_);
v___x_1607_ = l_Lean_Name_toString(v___x_1606_, v___x_1603_);
lean_inc(v_pivot_1599_);
v___x_1608_ = l_Lean_Name_toString(v_pivot_1599_, v___x_1603_);
v___x_1609_ = lean_string_dec_lt(v___x_1607_, v___x_1608_);
lean_dec_ref(v___x_1608_);
lean_dec_ref(v___x_1607_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1610_ = lean_unsigned_to_nat(1u);
v___x_1611_ = lean_nat_add(v_k_1602_, v___x_1610_);
lean_dec(v_k_1602_);
v_k_1602_ = v___x_1611_;
goto _start;
}
else
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1613_ = lean_array_fswap(v_as_1600_, v_i_1601_, v_k_1602_);
v___x_1614_ = lean_unsigned_to_nat(1u);
v___x_1615_ = lean_nat_add(v_i_1601_, v___x_1614_);
lean_dec(v_i_1601_);
v___x_1616_ = lean_nat_add(v_k_1602_, v___x_1614_);
lean_dec(v_k_1602_);
v_as_1600_ = v___x_1613_;
v_i_1601_ = v___x_1615_;
v_k_1602_ = v___x_1616_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg___boxed(lean_object* v_hi_1618_, lean_object* v_pivot_1619_, lean_object* v_as_1620_, lean_object* v_i_1621_, lean_object* v_k_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_1618_, v_pivot_1619_, v_as_1620_, v_i_1621_, v_k_1622_);
lean_dec(v_hi_1618_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(lean_object* v_n_1624_, lean_object* v_as_1625_, lean_object* v_lo_1626_, lean_object* v_hi_1627_){
_start:
{
lean_object* v___y_1629_; uint8_t v___x_1639_; 
v___x_1639_ = lean_nat_dec_lt(v_lo_1626_, v_hi_1627_);
if (v___x_1639_ == 0)
{
lean_dec(v_lo_1626_);
return v_as_1625_;
}
else
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v_mid_1642_; lean_object* v___y_1644_; lean_object* v___y_1650_; lean_object* v___x_1655_; lean_object* v___x_1656_; uint8_t v___x_1657_; 
v___x_1640_ = lean_nat_add(v_lo_1626_, v_hi_1627_);
v___x_1641_ = lean_unsigned_to_nat(1u);
v_mid_1642_ = lean_nat_shiftr(v___x_1640_, v___x_1641_);
lean_dec(v___x_1640_);
v___x_1655_ = lean_array_fget_borrowed(v_as_1625_, v_mid_1642_);
v___x_1656_ = lean_array_fget_borrowed(v_as_1625_, v_lo_1626_);
lean_inc(v___x_1656_);
lean_inc(v___x_1655_);
v___x_1657_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_1639_, v___x_1655_, v___x_1656_);
if (v___x_1657_ == 0)
{
v___y_1650_ = v_as_1625_;
goto v___jp_1649_;
}
else
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_array_fswap(v_as_1625_, v_lo_1626_, v_mid_1642_);
v___y_1650_ = v___x_1658_;
goto v___jp_1649_;
}
v___jp_1643_:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
v___x_1645_ = lean_array_fget_borrowed(v___y_1644_, v_mid_1642_);
v___x_1646_ = lean_array_fget_borrowed(v___y_1644_, v_hi_1627_);
lean_inc(v___x_1646_);
lean_inc(v___x_1645_);
v___x_1647_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_1639_, v___x_1645_, v___x_1646_);
if (v___x_1647_ == 0)
{
lean_dec(v_mid_1642_);
v___y_1629_ = v___y_1644_;
goto v___jp_1628_;
}
else
{
lean_object* v___x_1648_; 
v___x_1648_ = lean_array_fswap(v___y_1644_, v_mid_1642_, v_hi_1627_);
lean_dec(v_mid_1642_);
v___y_1629_ = v___x_1648_;
goto v___jp_1628_;
}
}
v___jp_1649_:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; 
v___x_1651_ = lean_array_fget_borrowed(v___y_1650_, v_hi_1627_);
v___x_1652_ = lean_array_fget_borrowed(v___y_1650_, v_lo_1626_);
lean_inc(v___x_1652_);
lean_inc(v___x_1651_);
v___x_1653_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_1639_, v___x_1651_, v___x_1652_);
if (v___x_1653_ == 0)
{
v___y_1644_ = v___y_1650_;
goto v___jp_1643_;
}
else
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_array_fswap(v___y_1650_, v_lo_1626_, v_hi_1627_);
v___y_1644_ = v___x_1654_;
goto v___jp_1643_;
}
}
}
v___jp_1628_:
{
lean_object* v_pivot_1630_; lean_object* v___x_1631_; lean_object* v_fst_1632_; lean_object* v_snd_1633_; uint8_t v___x_1634_; 
v_pivot_1630_ = lean_array_fget(v___y_1629_, v_hi_1627_);
lean_inc_n(v_lo_1626_, 2);
v___x_1631_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_1627_, v_pivot_1630_, v___y_1629_, v_lo_1626_, v_lo_1626_);
v_fst_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_fst_1632_);
v_snd_1633_ = lean_ctor_get(v___x_1631_, 1);
lean_inc(v_snd_1633_);
lean_dec_ref(v___x_1631_);
v___x_1634_ = lean_nat_dec_le(v_hi_1627_, v_fst_1632_);
if (v___x_1634_ == 0)
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1635_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_1624_, v_snd_1633_, v_lo_1626_, v_fst_1632_);
v___x_1636_ = lean_unsigned_to_nat(1u);
v___x_1637_ = lean_nat_add(v_fst_1632_, v___x_1636_);
lean_dec(v_fst_1632_);
v_as_1625_ = v___x_1635_;
v_lo_1626_ = v___x_1637_;
goto _start;
}
else
{
lean_dec(v_fst_1632_);
lean_dec(v_lo_1626_);
return v_snd_1633_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___boxed(lean_object* v_n_1659_, lean_object* v_as_1660_, lean_object* v_lo_1661_, lean_object* v_hi_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_1659_, v_as_1660_, v_lo_1661_, v_hi_1662_);
lean_dec(v_hi_1662_);
lean_dec(v_n_1659_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(lean_object* v_init_1664_, lean_object* v_x_1665_){
_start:
{
if (lean_obj_tag(v_x_1665_) == 0)
{
lean_object* v_k_1666_; lean_object* v_l_1667_; lean_object* v_r_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v_k_1666_ = lean_ctor_get(v_x_1665_, 1);
lean_inc(v_k_1666_);
v_l_1667_ = lean_ctor_get(v_x_1665_, 3);
lean_inc(v_l_1667_);
v_r_1668_ = lean_ctor_get(v_x_1665_, 4);
lean_inc(v_r_1668_);
lean_dec_ref_known(v_x_1665_, 5);
v___x_1669_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v_init_1664_, v_l_1667_);
v___x_1670_ = lean_array_push(v___x_1669_, v_k_1666_);
v_init_1664_ = v___x_1670_;
v_x_1665_ = v_r_1668_;
goto _start;
}
else
{
return v_init_1664_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(lean_object* v_a_1672_, lean_object* v_a_1673_){
_start:
{
if (lean_obj_tag(v_a_1672_) == 0)
{
lean_object* v___x_1674_; 
v___x_1674_ = l_List_reverse___redArg(v_a_1673_);
return v___x_1674_;
}
else
{
lean_object* v_head_1675_; lean_object* v_tail_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1685_; 
v_head_1675_ = lean_ctor_get(v_a_1672_, 0);
v_tail_1676_ = lean_ctor_get(v_a_1672_, 1);
v_isSharedCheck_1685_ = !lean_is_exclusive(v_a_1672_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1678_ = v_a_1672_;
v_isShared_1679_ = v_isSharedCheck_1685_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_tail_1676_);
lean_inc(v_head_1675_);
lean_dec(v_a_1672_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1685_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1680_; lean_object* v___x_1682_; 
v___x_1680_ = l_Lean_Level_param___override(v_head_1675_);
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 1, v_a_1673_);
lean_ctor_set(v___x_1678_, 0, v___x_1680_);
v___x_1682_ = v___x_1678_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1680_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v_a_1673_);
v___x_1682_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
v_a_1672_ = v_tail_1676_;
v_a_1673_ = v___x_1682_;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(lean_object* v_x1_1686_, lean_object* v_x2_1687_){
_start:
{
lean_object* v_fst_1688_; lean_object* v_fst_1689_; uint8_t v___x_1690_; 
v_fst_1688_ = lean_ctor_get(v_x1_1686_, 0);
v_fst_1689_ = lean_ctor_get(v_x2_1687_, 0);
v___x_1690_ = l_Lean_Name_quickLt(v_fst_1688_, v_fst_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0___boxed(lean_object* v_x1_1691_, lean_object* v_x2_1692_){
_start:
{
uint8_t v_res_1693_; lean_object* v_r_1694_; 
v_res_1693_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_x1_1691_, v_x2_1692_);
lean_dec_ref(v_x2_1692_);
lean_dec_ref(v_x1_1691_);
v_r_1694_ = lean_box(v_res_1693_);
return v_r_1694_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(lean_object* v_as_1695_, lean_object* v_k_1696_, lean_object* v_x_1697_, lean_object* v_x_1698_){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v_m_1701_; lean_object* v_a_1702_; uint8_t v___x_1703_; 
v___x_1699_ = lean_nat_add(v_x_1697_, v_x_1698_);
v___x_1700_ = lean_unsigned_to_nat(1u);
v_m_1701_ = lean_nat_shiftr(v___x_1699_, v___x_1700_);
lean_dec(v___x_1699_);
v_a_1702_ = lean_array_fget_borrowed(v_as_1695_, v_m_1701_);
v___x_1703_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_a_1702_, v_k_1696_);
if (v___x_1703_ == 0)
{
uint8_t v___x_1704_; 
lean_dec(v_x_1698_);
v___x_1704_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_k_1696_, v_a_1702_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1705_; 
lean_dec(v_m_1701_);
lean_dec(v_x_1697_);
lean_inc(v_a_1702_);
v___x_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1705_, 0, v_a_1702_);
return v___x_1705_;
}
else
{
lean_object* v___x_1706_; uint8_t v___x_1707_; 
v___x_1706_ = lean_unsigned_to_nat(0u);
v___x_1707_ = lean_nat_dec_eq(v_m_1701_, v___x_1706_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; uint8_t v___x_1709_; 
v___x_1708_ = lean_nat_sub(v_m_1701_, v___x_1700_);
lean_dec(v_m_1701_);
v___x_1709_ = lean_nat_dec_lt(v___x_1708_, v_x_1697_);
if (v___x_1709_ == 0)
{
v_x_1698_ = v___x_1708_;
goto _start;
}
else
{
lean_object* v___x_1711_; 
lean_dec(v___x_1708_);
lean_dec(v_x_1697_);
v___x_1711_ = lean_box(0);
return v___x_1711_;
}
}
else
{
lean_object* v___x_1712_; 
lean_dec(v_m_1701_);
lean_dec(v_x_1697_);
v___x_1712_ = lean_box(0);
return v___x_1712_;
}
}
}
else
{
lean_object* v___x_1713_; uint8_t v___x_1714_; 
lean_dec(v_x_1697_);
v___x_1713_ = lean_nat_add(v_m_1701_, v___x_1700_);
lean_dec(v_m_1701_);
v___x_1714_ = lean_nat_dec_le(v___x_1713_, v_x_1698_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1715_; 
lean_dec(v___x_1713_);
lean_dec(v_x_1698_);
v___x_1715_ = lean_box(0);
return v___x_1715_;
}
else
{
v_x_1697_ = v___x_1713_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___boxed(lean_object* v_as_1717_, lean_object* v_k_1718_, lean_object* v_x_1719_, lean_object* v_x_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_1717_, v_k_1718_, v_x_1719_, v_x_1720_);
lean_dec_ref(v_k_1718_);
lean_dec_ref(v_as_1717_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(lean_object* v_tac_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v___x_1726_; lean_object* v_env_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1726_ = lean_st_ref_get(v___y_1724_);
v_env_1730_ = lean_ctor_get(v___x_1726_, 0);
lean_inc_ref(v_env_1730_);
lean_dec(v___x_1726_);
v___x_1731_ = lean_box(1);
v___x_1732_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1730_, v_tac_1723_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v___x_1733_; lean_object* v_toEnvExtension_1734_; lean_object* v_asyncMode_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1733_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_1734_ = lean_ctor_get(v___x_1733_, 0);
v_asyncMode_1735_ = lean_ctor_get(v_toEnvExtension_1734_, 2);
v___x_1736_ = lean_box(0);
v___x_1737_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1731_, v___x_1733_, v_env_1730_, v_asyncMode_1735_, v___x_1736_);
v___x_1738_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1737_, v_tac_1723_);
lean_dec(v_tac_1723_);
lean_dec(v___x_1737_);
v___x_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
return v___x_1739_;
}
else
{
lean_object* v_val_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1768_; 
v_val_1740_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1742_ = v___x_1732_;
v_isShared_1743_ = v_isSharedCheck_1768_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_val_1740_);
lean_dec(v___x_1732_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1768_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1744_; uint8_t v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; 
v___x_1744_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v___x_1745_ = 0;
v___x_1746_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1731_, v___x_1744_, v_env_1730_, v_val_1740_, v___x_1745_);
lean_dec(v_val_1740_);
lean_dec_ref(v_env_1730_);
v___x_1747_ = lean_unsigned_to_nat(0u);
v___x_1748_ = lean_array_get_size(v___x_1746_);
v___x_1749_ = lean_nat_dec_lt(v___x_1747_, v___x_1748_);
if (v___x_1749_ == 0)
{
lean_dec_ref(v___x_1746_);
lean_del_object(v___x_1742_);
lean_dec(v_tac_1723_);
goto v___jp_1727_;
}
else
{
lean_object* v___x_1750_; lean_object* v___x_1751_; uint8_t v___x_1752_; 
v___x_1750_ = lean_unsigned_to_nat(1u);
v___x_1751_ = lean_nat_sub(v___x_1748_, v___x_1750_);
v___x_1752_ = lean_nat_dec_le(v___x_1747_, v___x_1751_);
if (v___x_1752_ == 0)
{
lean_dec(v___x_1751_);
lean_dec_ref(v___x_1746_);
lean_del_object(v___x_1742_);
lean_dec(v_tac_1723_);
goto v___jp_1727_;
}
else
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1753_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0));
v___x_1754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1754_, 0, v_tac_1723_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
v___x_1755_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v___x_1746_, v___x_1754_, v___x_1747_, v___x_1751_);
lean_dec_ref_known(v___x_1754_, 2);
lean_dec_ref(v___x_1746_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_del_object(v___x_1742_);
goto v___jp_1727_;
}
else
{
lean_object* v_val_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1767_; 
v_val_1756_ = lean_ctor_get(v___x_1755_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1755_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1758_ = v___x_1755_;
v_isShared_1759_ = v_isSharedCheck_1767_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_val_1756_);
lean_dec(v___x_1755_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1767_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v_snd_1760_; lean_object* v___x_1762_; 
v_snd_1760_ = lean_ctor_get(v_val_1756_, 1);
lean_inc(v_snd_1760_);
lean_dec(v_val_1756_);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v_snd_1760_);
v___x_1762_ = v___x_1758_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_snd_1760_);
v___x_1762_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
lean_object* v___x_1764_; 
if (v_isShared_1743_ == 0)
{
lean_ctor_set_tag(v___x_1742_, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1762_);
v___x_1764_ = v___x_1742_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
}
}
}
}
v___jp_1727_:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1728_ = lean_box(0);
v___x_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
return v___x_1729_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___boxed(lean_object* v_tac_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_1769_, v___y_1770_);
lean_dec(v___y_1770_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(lean_object* v_t_1773_, lean_object* v_k_1774_){
_start:
{
if (lean_obj_tag(v_t_1773_) == 0)
{
lean_object* v_k_1775_; lean_object* v_v_1776_; lean_object* v_l_1777_; lean_object* v_r_1778_; uint8_t v___x_1779_; 
v_k_1775_ = lean_ctor_get(v_t_1773_, 1);
v_v_1776_ = lean_ctor_get(v_t_1773_, 2);
v_l_1777_ = lean_ctor_get(v_t_1773_, 3);
v_r_1778_ = lean_ctor_get(v_t_1773_, 4);
v___x_1779_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1774_, v_k_1775_);
switch(v___x_1779_)
{
case 0:
{
v_t_1773_ = v_l_1777_;
goto _start;
}
case 1:
{
lean_object* v___x_1781_; 
lean_inc(v_v_1776_);
v___x_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1781_, 0, v_v_1776_);
return v___x_1781_;
}
default: 
{
v_t_1773_ = v_r_1778_;
goto _start;
}
}
}
else
{
lean_object* v___x_1783_; 
v___x_1783_ = lean_box(0);
return v___x_1783_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg___boxed(lean_object* v_t_1784_, lean_object* v_k_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_t_1784_, v_k_1785_);
lean_dec(v_k_1785_);
lean_dec(v_t_1784_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(lean_object* v_a_1787_, lean_object* v_x_1788_){
_start:
{
if (lean_obj_tag(v_x_1788_) == 0)
{
lean_object* v___x_1789_; 
v___x_1789_ = lean_box(0);
return v___x_1789_;
}
else
{
lean_object* v_key_1790_; lean_object* v_value_1791_; lean_object* v_tail_1792_; uint8_t v___x_1793_; 
v_key_1790_ = lean_ctor_get(v_x_1788_, 0);
v_value_1791_ = lean_ctor_get(v_x_1788_, 1);
v_tail_1792_ = lean_ctor_get(v_x_1788_, 2);
v___x_1793_ = lean_name_eq(v_key_1790_, v_a_1787_);
if (v___x_1793_ == 0)
{
v_x_1788_ = v_tail_1792_;
goto _start;
}
else
{
lean_object* v___x_1795_; 
lean_inc(v_value_1791_);
v___x_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1795_, 0, v_value_1791_);
return v___x_1795_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg___boxed(lean_object* v_a_1796_, lean_object* v_x_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_1796_, v_x_1797_);
lean_dec(v_x_1797_);
lean_dec(v_a_1796_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(lean_object* v_m_1799_, lean_object* v_a_1800_){
_start:
{
lean_object* v_buckets_1801_; lean_object* v___x_1802_; uint64_t v___y_1804_; 
v_buckets_1801_ = lean_ctor_get(v_m_1799_, 1);
v___x_1802_ = lean_array_get_size(v_buckets_1801_);
if (lean_obj_tag(v_a_1800_) == 0)
{
uint64_t v___x_1818_; 
v___x_1818_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0);
v___y_1804_ = v___x_1818_;
goto v___jp_1803_;
}
else
{
uint64_t v_hash_1819_; 
v_hash_1819_ = lean_ctor_get_uint64(v_a_1800_, sizeof(void*)*2);
v___y_1804_ = v_hash_1819_;
goto v___jp_1803_;
}
v___jp_1803_:
{
uint64_t v___x_1805_; uint64_t v___x_1806_; uint64_t v_fold_1807_; uint64_t v___x_1808_; uint64_t v___x_1809_; uint64_t v___x_1810_; size_t v___x_1811_; size_t v___x_1812_; size_t v___x_1813_; size_t v___x_1814_; size_t v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1805_ = 32ULL;
v___x_1806_ = lean_uint64_shift_right(v___y_1804_, v___x_1805_);
v_fold_1807_ = lean_uint64_xor(v___y_1804_, v___x_1806_);
v___x_1808_ = 16ULL;
v___x_1809_ = lean_uint64_shift_right(v_fold_1807_, v___x_1808_);
v___x_1810_ = lean_uint64_xor(v_fold_1807_, v___x_1809_);
v___x_1811_ = lean_uint64_to_usize(v___x_1810_);
v___x_1812_ = lean_usize_of_nat(v___x_1802_);
v___x_1813_ = ((size_t)1ULL);
v___x_1814_ = lean_usize_sub(v___x_1812_, v___x_1813_);
v___x_1815_ = lean_usize_land(v___x_1811_, v___x_1814_);
v___x_1816_ = lean_array_uget_borrowed(v_buckets_1801_, v___x_1815_);
v___x_1817_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_1800_, v___x_1816_);
return v___x_1817_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg___boxed(lean_object* v_m_1820_, lean_object* v_a_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_m_1820_, v_a_1821_);
lean_dec(v_a_1821_);
lean_dec_ref(v_m_1820_);
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(lean_object* v_keys_1823_, lean_object* v_vals_1824_, lean_object* v_i_1825_, lean_object* v_k_1826_){
_start:
{
lean_object* v___x_1827_; uint8_t v___x_1828_; 
v___x_1827_ = lean_array_get_size(v_keys_1823_);
v___x_1828_ = lean_nat_dec_lt(v_i_1825_, v___x_1827_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1829_; 
lean_dec(v_i_1825_);
v___x_1829_ = lean_box(0);
return v___x_1829_;
}
else
{
lean_object* v_k_x27_1830_; uint8_t v___x_1831_; 
v_k_x27_1830_ = lean_array_fget_borrowed(v_keys_1823_, v_i_1825_);
v___x_1831_ = lean_name_eq(v_k_1826_, v_k_x27_1830_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = lean_unsigned_to_nat(1u);
v___x_1833_ = lean_nat_add(v_i_1825_, v___x_1832_);
lean_dec(v_i_1825_);
v_i_1825_ = v___x_1833_;
goto _start;
}
else
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1835_ = lean_array_fget_borrowed(v_vals_1824_, v_i_1825_);
lean_dec(v_i_1825_);
lean_inc(v___x_1835_);
v___x_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
return v___x_1836_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg___boxed(lean_object* v_keys_1837_, lean_object* v_vals_1838_, lean_object* v_i_1839_, lean_object* v_k_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_1837_, v_vals_1838_, v_i_1839_, v_k_1840_);
lean_dec(v_k_1840_);
lean_dec_ref(v_vals_1838_);
lean_dec_ref(v_keys_1837_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(lean_object* v_x_1842_, size_t v_x_1843_, lean_object* v_x_1844_){
_start:
{
if (lean_obj_tag(v_x_1842_) == 0)
{
lean_object* v_es_1845_; lean_object* v___x_1846_; size_t v___x_1847_; size_t v___x_1848_; lean_object* v_j_1849_; lean_object* v___x_1850_; 
v_es_1845_ = lean_ctor_get(v_x_1842_, 0);
v___x_1846_ = lean_box(2);
v___x_1847_ = ((size_t)31ULL);
v___x_1848_ = lean_usize_land(v_x_1843_, v___x_1847_);
v_j_1849_ = lean_usize_to_nat(v___x_1848_);
v___x_1850_ = lean_array_get_borrowed(v___x_1846_, v_es_1845_, v_j_1849_);
lean_dec(v_j_1849_);
switch(lean_obj_tag(v___x_1850_))
{
case 0:
{
lean_object* v_key_1851_; lean_object* v_val_1852_; uint8_t v___x_1853_; 
v_key_1851_ = lean_ctor_get(v___x_1850_, 0);
v_val_1852_ = lean_ctor_get(v___x_1850_, 1);
v___x_1853_ = lean_name_eq(v_x_1844_, v_key_1851_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; 
v___x_1854_ = lean_box(0);
return v___x_1854_;
}
else
{
lean_object* v___x_1855_; 
lean_inc(v_val_1852_);
v___x_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1855_, 0, v_val_1852_);
return v___x_1855_;
}
}
case 1:
{
lean_object* v_node_1856_; size_t v___x_1857_; size_t v___x_1858_; 
v_node_1856_ = lean_ctor_get(v___x_1850_, 0);
v___x_1857_ = ((size_t)5ULL);
v___x_1858_ = lean_usize_shift_right(v_x_1843_, v___x_1857_);
v_x_1842_ = v_node_1856_;
v_x_1843_ = v___x_1858_;
goto _start;
}
default: 
{
lean_object* v___x_1860_; 
v___x_1860_ = lean_box(0);
return v___x_1860_;
}
}
}
else
{
lean_object* v_ks_1861_; lean_object* v_vs_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v_ks_1861_ = lean_ctor_get(v_x_1842_, 0);
v_vs_1862_ = lean_ctor_get(v_x_1842_, 1);
v___x_1863_ = lean_unsigned_to_nat(0u);
v___x_1864_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_ks_1861_, v_vs_1862_, v___x_1863_, v_x_1844_);
return v___x_1864_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_x_1865_, lean_object* v_x_1866_, lean_object* v_x_1867_){
_start:
{
size_t v_x_17396__boxed_1868_; lean_object* v_res_1869_; 
v_x_17396__boxed_1868_ = lean_unbox_usize(v_x_1866_);
lean_dec(v_x_1866_);
v_res_1869_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_1865_, v_x_17396__boxed_1868_, v_x_1867_);
lean_dec(v_x_1867_);
lean_dec_ref(v_x_1865_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(lean_object* v_x_1870_, lean_object* v_x_1871_){
_start:
{
uint64_t v___y_1873_; 
if (lean_obj_tag(v_x_1871_) == 0)
{
uint64_t v___x_1876_; 
v___x_1876_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0);
v___y_1873_ = v___x_1876_;
goto v___jp_1872_;
}
else
{
uint64_t v_hash_1877_; 
v_hash_1877_ = lean_ctor_get_uint64(v_x_1871_, sizeof(void*)*2);
v___y_1873_ = v_hash_1877_;
goto v___jp_1872_;
}
v___jp_1872_:
{
size_t v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = lean_uint64_to_usize(v___y_1873_);
v___x_1875_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_1870_, v___x_1874_, v_x_1871_);
return v___x_1875_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg___boxed(lean_object* v_x_1878_, lean_object* v_x_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_1878_, v_x_1879_);
lean_dec(v_x_1879_);
lean_dec_ref(v_x_1878_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(lean_object* v_x_1881_, lean_object* v_x_1882_){
_start:
{
uint8_t v_stage_u2081_1883_; 
v_stage_u2081_1883_ = lean_ctor_get_uint8(v_x_1881_, sizeof(void*)*2);
if (v_stage_u2081_1883_ == 0)
{
lean_object* v_map_u2081_1884_; lean_object* v_map_u2082_1885_; lean_object* v___x_1886_; 
v_map_u2081_1884_ = lean_ctor_get(v_x_1881_, 0);
v_map_u2082_1885_ = lean_ctor_get(v_x_1881_, 1);
v___x_1886_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_map_u2081_1884_, v_x_1882_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v___x_1887_; 
v___x_1887_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_map_u2082_1885_, v_x_1882_);
return v___x_1887_;
}
else
{
return v___x_1886_;
}
}
else
{
lean_object* v_map_u2081_1888_; lean_object* v___x_1889_; 
v_map_u2081_1888_ = lean_ctor_get(v_x_1881_, 0);
v___x_1889_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_map_u2081_1888_, v_x_1882_);
return v___x_1889_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg___boxed(lean_object* v_x_1890_, lean_object* v_x_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_x_1890_, v_x_1891_);
lean_dec(v_x_1891_);
lean_dec_ref(v_x_1890_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(lean_object* v_firsts_1893_, lean_object* v_n_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1913_; lean_object* v_val_1914_; lean_object* v___x_1916_; lean_object* v___y_1918_; lean_object* v_env_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1916_ = lean_st_ref_get(v___y_1896_);
v_env_1933_ = lean_ctor_get(v___x_1916_, 0);
lean_inc_ref(v_env_1933_);
lean_dec(v___x_1916_);
v___x_1934_ = l_Lean_Environment_constants(v_env_1933_);
v___x_1935_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v___x_1934_, v_n_1894_);
lean_dec_ref(v___x_1934_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v___x_1936_; 
v___x_1936_ = lean_box(0);
v___y_1918_ = v___x_1936_;
goto v___jp_1917_;
}
else
{
lean_object* v_val_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v_val_1937_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_val_1937_);
lean_dec_ref_known(v___x_1935_, 1);
v___x_1938_ = l_Lean_ConstantInfo_levelParams(v_val_1937_);
lean_dec(v_val_1937_);
v___x_1939_ = lean_box(0);
v___x_1940_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(v___x_1938_, v___x_1939_);
v___y_1918_ = v___x_1940_;
goto v___jp_1917_;
}
v___jp_1898_:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; uint8_t v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1901_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
v___x_1902_ = l_Lean_Expr_const___override(v_n_1894_, v___y_1899_);
v___x_1903_ = lean_unsigned_to_nat(32u);
v___x_1904_ = lean_mk_empty_array_with_capacity(v___x_1903_);
lean_dec_ref(v___x_1904_);
v___x_1905_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___closed__2);
v___x_1906_ = lean_box(0);
v___x_1907_ = 0;
v___x_1908_ = l_Lean_MessageData_withExprHover(v___y_1900_, v___x_1902_, v___x_1905_, v___x_1906_, v___x_1906_, v___x_1906_, v___x_1907_);
v___x_1909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1901_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
v___x_1910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1909_);
lean_ctor_set(v___x_1910_, 1, v___x_1901_);
v___x_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1910_);
return v___x_1911_;
}
v___jp_1912_:
{
lean_object* v___x_1915_; 
v___x_1915_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1915_, 0, v_val_1914_);
v___y_1899_ = v___y_1913_;
v___y_1900_ = v___x_1915_;
goto v___jp_1898_;
}
v___jp_1917_:
{
lean_object* v___x_1919_; lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1932_; 
lean_inc(v_n_1894_);
v___x_1919_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_n_1894_, v___y_1896_);
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1919_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1922_ = v___x_1919_;
v_isShared_1923_ = v_isSharedCheck_1932_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1919_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1932_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
if (lean_obj_tag(v_a_1920_) == 0)
{
lean_object* v___x_1924_; 
v___x_1924_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_firsts_1893_, v_n_1894_);
if (lean_obj_tag(v___x_1924_) == 0)
{
uint8_t v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1928_; 
v___x_1925_ = 1;
lean_inc(v_n_1894_);
v___x_1926_ = l_Lean_Name_toString(v_n_1894_, v___x_1925_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set_tag(v___x_1922_, 3);
lean_ctor_set(v___x_1922_, 0, v___x_1926_);
v___x_1928_ = v___x_1922_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1926_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
v___y_1899_ = v___y_1918_;
v___y_1900_ = v___x_1928_;
goto v___jp_1898_;
}
}
else
{
lean_object* v_val_1930_; 
lean_del_object(v___x_1922_);
v_val_1930_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_val_1930_);
lean_dec_ref_known(v___x_1924_, 1);
v___y_1913_ = v___y_1918_;
v_val_1914_ = v_val_1930_;
goto v___jp_1912_;
}
}
else
{
lean_object* v_val_1931_; 
lean_del_object(v___x_1922_);
v_val_1931_ = lean_ctor_get(v_a_1920_, 0);
lean_inc(v_val_1931_);
lean_dec_ref_known(v_a_1920_, 1);
v___y_1913_ = v___y_1918_;
v_val_1914_ = v_val_1931_;
goto v___jp_1912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6___boxed(lean_object* v_firsts_1941_, lean_object* v_n_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_firsts_1941_, v_n_1942_, v___y_1943_, v___y_1944_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec(v_firsts_1941_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(lean_object* v_a_1947_, lean_object* v_x_1948_, lean_object* v_x_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
if (lean_obj_tag(v_x_1948_) == 0)
{
lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1953_ = l_List_reverse___redArg(v_x_1949_);
v___x_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1953_);
return v___x_1954_;
}
else
{
lean_object* v_head_1955_; lean_object* v_tail_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1974_; 
v_head_1955_ = lean_ctor_get(v_x_1948_, 0);
v_tail_1956_ = lean_ctor_get(v_x_1948_, 1);
v_isSharedCheck_1974_ = !lean_is_exclusive(v_x_1948_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1958_ = v_x_1948_;
v_isShared_1959_ = v_isSharedCheck_1974_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_tail_1956_);
lean_inc(v_head_1955_);
lean_dec(v_x_1948_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1974_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1960_; 
v___x_1960_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_a_1947_, v_head_1955_, v___y_1950_, v___y_1951_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_a_1961_; lean_object* v___x_1963_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_a_1961_);
lean_dec_ref_known(v___x_1960_, 1);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 1, v_x_1949_);
lean_ctor_set(v___x_1958_, 0, v_a_1961_);
v___x_1963_ = v___x_1958_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1961_);
lean_ctor_set(v_reuseFailAlloc_1965_, 1, v_x_1949_);
v___x_1963_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
v_x_1948_ = v_tail_1956_;
v_x_1949_ = v___x_1963_;
goto _start;
}
}
else
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
lean_del_object(v___x_1958_);
lean_dec(v_tail_1956_);
lean_dec(v_x_1949_);
v_a_1966_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___x_1960_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___x_1960_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
if (v_isShared_1969_ == 0)
{
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7___boxed(lean_object* v_a_1975_, lean_object* v_x_1976_, lean_object* v_x_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_1975_, v_x_1976_, v_x_1977_, v___y_1978_, v___y_1979_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec(v_a_1975_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(lean_object* v_val_1982_, lean_object* v___x_1983_, lean_object* v___x_1984_, lean_object* v_a_1985_, lean_object* v_b_1986_){
_start:
{
lean_object* v_it_1988_; lean_object* v_startInclusive_1989_; lean_object* v_endExclusive_1990_; 
if (lean_obj_tag(v_a_1985_) == 0)
{
lean_object* v_currPos_1995_; lean_object* v_searcher_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2022_; 
v_currPos_1995_ = lean_ctor_get(v_a_1985_, 0);
v_searcher_1996_ = lean_ctor_get(v_a_1985_, 1);
v_isSharedCheck_2022_ = !lean_is_exclusive(v_a_1985_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_1998_ = v_a_1985_;
v_isShared_1999_ = v_isSharedCheck_2022_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_searcher_1996_);
lean_inc(v_currPos_1995_);
lean_dec(v_a_1985_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2022_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v_startInclusive_2000_; lean_object* v_endExclusive_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; 
v_startInclusive_2000_ = lean_ctor_get(v___x_1983_, 1);
v_endExclusive_2001_ = lean_ctor_get(v___x_1983_, 2);
v___x_2002_ = lean_nat_sub(v_endExclusive_2001_, v_startInclusive_2000_);
v___x_2003_ = lean_nat_dec_eq(v_searcher_1996_, v___x_2002_);
lean_dec(v___x_2002_);
if (v___x_2003_ == 0)
{
uint32_t v___x_2004_; uint32_t v___x_2005_; uint8_t v___x_2006_; 
v___x_2004_ = 10;
v___x_2005_ = lean_string_utf8_get_fast(v_val_1982_, v_searcher_1996_);
v___x_2006_ = lean_uint32_dec_eq(v___x_2005_, v___x_2004_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2007_; lean_object* v___x_2009_; 
v___x_2007_ = lean_string_utf8_next_fast(v_val_1982_, v_searcher_1996_);
lean_dec(v_searcher_1996_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 1, v___x_2007_);
v___x_2009_ = v___x_1998_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_currPos_1995_);
lean_ctor_set(v_reuseFailAlloc_2011_, 1, v___x_2007_);
v___x_2009_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
v_a_1985_ = v___x_2009_;
goto _start;
}
}
else
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v_slice_2015_; lean_object* v_nextIt_2017_; 
v___x_2012_ = lean_string_utf8_next_fast(v_val_1982_, v_searcher_1996_);
v___x_2013_ = lean_nat_sub(v___x_2012_, v_searcher_1996_);
v___x_2014_ = lean_nat_add(v_searcher_1996_, v___x_2013_);
lean_dec(v___x_2013_);
v_slice_2015_ = l_String_Slice_subslice_x21(v___x_1983_, v_currPos_1995_, v_searcher_1996_);
lean_inc(v___x_2014_);
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 1, v___x_2014_);
lean_ctor_set(v___x_1998_, 0, v___x_2014_);
v_nextIt_2017_ = v___x_1998_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2014_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v___x_2014_);
v_nextIt_2017_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
lean_object* v_startInclusive_2018_; lean_object* v_endExclusive_2019_; 
v_startInclusive_2018_ = lean_ctor_get(v_slice_2015_, 0);
lean_inc(v_startInclusive_2018_);
v_endExclusive_2019_ = lean_ctor_get(v_slice_2015_, 1);
lean_inc(v_endExclusive_2019_);
lean_dec_ref(v_slice_2015_);
v_it_1988_ = v_nextIt_2017_;
v_startInclusive_1989_ = v_startInclusive_2018_;
v_endExclusive_1990_ = v_endExclusive_2019_;
goto v___jp_1987_;
}
}
}
else
{
lean_object* v___x_2021_; 
lean_del_object(v___x_1998_);
lean_dec(v_searcher_1996_);
v___x_2021_ = lean_box(1);
lean_inc(v___x_1984_);
v_it_1988_ = v___x_2021_;
v_startInclusive_1989_ = v_currPos_1995_;
v_endExclusive_1990_ = v___x_1984_;
goto v___jp_1987_;
}
}
}
else
{
lean_dec(v___x_1984_);
return v_b_1986_;
}
v___jp_1987_:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1991_ = lean_string_utf8_extract(v_val_1982_, v_startInclusive_1989_, v_endExclusive_1990_);
lean_dec(v_endExclusive_1990_);
lean_dec(v_startInclusive_1989_);
v___x_1992_ = l_Lean_stringToMessageData(v___x_1991_);
v___x_1993_ = lean_array_push(v_b_1986_, v___x_1992_);
v_a_1985_ = v_it_1988_;
v_b_1986_ = v___x_1993_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg___boxed(lean_object* v_val_2023_, lean_object* v___x_2024_, lean_object* v___x_2025_, lean_object* v_a_2026_, lean_object* v_b_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2023_, v___x_2024_, v___x_2025_, v_a_2026_, v_b_2027_);
lean_dec_ref(v___x_2024_);
lean_dec_ref(v_val_2023_);
return v_res_2028_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2(void){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1));
v___x_2033_ = l_Lean_stringToMessageData(v___x_2032_);
return v___x_2033_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4(void){
_start:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2035_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3));
v___x_2036_ = l_Lean_stringToMessageData(v___x_2035_);
return v___x_2036_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6(void){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5));
v___x_2039_ = l_Lean_stringToMessageData(v___x_2038_);
return v___x_2039_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9(void){
_start:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8));
v___x_2044_ = l_Lean_MessageData_ofFormat(v___x_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_x_2047_, lean_object* v_x_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
if (lean_obj_tag(v_x_2047_) == 0)
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2052_ = l_List_reverse___redArg(v_x_2048_);
v___x_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
return v___x_2053_;
}
else
{
lean_object* v_head_2054_; lean_object* v_tail_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2152_; 
v_head_2054_ = lean_ctor_get(v_x_2047_, 0);
v_tail_2055_ = lean_ctor_get(v_x_2047_, 1);
v_isSharedCheck_2152_ = !lean_is_exclusive(v_x_2047_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2057_ = v_x_2047_;
v_isShared_2058_ = v_isSharedCheck_2152_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_tail_2055_);
lean_inc(v_head_2054_);
lean_dec(v_x_2047_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2152_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v_snd_2072_; lean_object* v_fst_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2151_; 
v_snd_2072_ = lean_ctor_get(v_head_2054_, 1);
v_fst_2073_ = lean_ctor_get(v_head_2054_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v_head_2054_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2075_ = v_head_2054_;
v_isShared_2076_ = v_isSharedCheck_2151_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_snd_2072_);
lean_inc(v_fst_2073_);
lean_dec(v_head_2054_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2151_;
goto v_resetjp_2074_;
}
v___jp_2059_:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___y_2062_);
lean_ctor_set(v___x_2064_, 1, v___y_2063_);
v___x_2065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2064_);
lean_ctor_set(v___x_2065_, 1, v___y_2060_);
v___x_2066_ = l_Lean_MessageData_nestD(v___x_2065_);
lean_inc_ref(v___y_2061_);
v___x_2067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___y_2061_);
lean_ctor_set(v___x_2067_, 1, v___x_2066_);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 1, v_x_2048_);
lean_ctor_set(v___x_2057_, 0, v___x_2067_);
v___x_2069_ = v___x_2057_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2067_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v_x_2048_);
v___x_2069_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
v_x_2047_ = v_tail_2055_;
v_x_2048_ = v___x_2069_;
goto _start;
}
}
v_resetjp_2074_:
{
lean_object* v_fst_2077_; lean_object* v_snd_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2150_; 
v_fst_2077_ = lean_ctor_get(v_snd_2072_, 0);
v_snd_2078_ = lean_ctor_get(v_snd_2072_, 1);
v_isSharedCheck_2150_ = !lean_is_exclusive(v_snd_2072_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2080_ = v_snd_2072_;
v_isShared_2081_ = v_isSharedCheck_2150_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_snd_2078_);
lean_inc(v_fst_2077_);
lean_dec(v_snd_2072_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2150_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; lean_object* v_a_2105_; lean_object* v___y_2121_; lean_object* v___x_2130_; 
v___x_2130_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_2046_, v_fst_2073_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v___x_2131_; 
v___x_2131_ = l_Lean_MessageData_nil;
v_a_2105_ = v___x_2131_;
goto v___jp_2104_;
}
else
{
lean_object* v_val_2132_; 
v_val_2132_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_val_2132_);
lean_dec_ref_known(v___x_2130_, 1);
if (lean_obj_tag(v_val_2132_) == 0)
{
lean_object* v_size_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___y_2138_; lean_object* v___y_2139_; lean_object* v___x_2141_; uint8_t v___x_2142_; 
v_size_2133_ = lean_ctor_get(v_val_2132_, 0);
v___x_2134_ = lean_mk_empty_array_with_capacity(v_size_2133_);
v___x_2135_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v___x_2134_, v_val_2132_);
v___x_2136_ = lean_array_get_size(v___x_2135_);
v___x_2141_ = lean_unsigned_to_nat(0u);
v___x_2142_ = lean_nat_dec_eq(v___x_2136_, v___x_2141_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___y_2146_; uint8_t v___x_2148_; 
v___x_2143_ = lean_unsigned_to_nat(1u);
v___x_2144_ = lean_nat_sub(v___x_2136_, v___x_2143_);
v___x_2148_ = lean_nat_dec_le(v___x_2141_, v___x_2144_);
if (v___x_2148_ == 0)
{
lean_inc(v___x_2144_);
v___y_2146_ = v___x_2144_;
goto v___jp_2145_;
}
else
{
v___y_2146_ = v___x_2141_;
goto v___jp_2145_;
}
v___jp_2145_:
{
uint8_t v___x_2147_; 
v___x_2147_ = lean_nat_dec_le(v___y_2146_, v___x_2144_);
if (v___x_2147_ == 0)
{
lean_dec(v___x_2144_);
lean_inc(v___y_2146_);
v___y_2138_ = v___y_2146_;
v___y_2139_ = v___y_2146_;
goto v___jp_2137_;
}
else
{
v___y_2138_ = v___y_2146_;
v___y_2139_ = v___x_2144_;
goto v___jp_2137_;
}
}
}
else
{
v___y_2121_ = v___x_2135_;
goto v___jp_2120_;
}
v___jp_2137_:
{
lean_object* v___x_2140_; 
v___x_2140_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v___x_2136_, v___x_2135_, v___y_2138_, v___y_2139_);
lean_dec(v___y_2139_);
v___y_2121_ = v___x_2140_;
goto v___jp_2120_;
}
}
else
{
lean_object* v___x_2149_; 
v___x_2149_ = l_Lean_MessageData_nil;
v_a_2105_ = v___x_2149_;
goto v___jp_2104_;
}
}
v___jp_2082_:
{
lean_object* v___x_2088_; 
if (v_isShared_2081_ == 0)
{
lean_ctor_set_tag(v___x_2080_, 7);
lean_ctor_set(v___x_2080_, 1, v___y_2086_);
lean_ctor_set(v___x_2080_, 0, v___y_2084_);
v___x_2088_ = v___x_2080_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___y_2084_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v___y_2086_);
v___x_2088_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
if (lean_obj_tag(v_snd_2078_) == 0)
{
lean_object* v___x_2089_; 
lean_del_object(v___x_2075_);
v___x_2089_ = l_Lean_MessageData_nil;
v___y_2060_ = v___y_2083_;
v___y_2061_ = v___y_2085_;
v___y_2062_ = v___x_2088_;
v___y_2063_ = v___x_2089_;
goto v___jp_2059_;
}
else
{
lean_object* v_val_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2101_; 
v_val_2090_ = lean_ctor_get(v_snd_2078_, 0);
lean_inc_n(v_val_2090_, 2);
lean_dec_ref_known(v_snd_2078_, 1);
v___x_2091_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2092_ = lean_unsigned_to_nat(0u);
v___x_2093_ = lean_string_utf8_byte_size(v_val_2090_);
v___x_2094_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2094_, 0, v_val_2090_);
lean_ctor_set(v___x_2094_, 1, v___x_2092_);
lean_ctor_set(v___x_2094_, 2, v___x_2093_);
v___x_2095_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v___x_2094_);
v___x_2096_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0));
v___x_2097_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2090_, v___x_2094_, v___x_2093_, v___x_2095_, v___x_2096_);
lean_dec_ref_known(v___x_2094_, 3);
lean_dec(v_val_2090_);
v___x_2098_ = lean_array_to_list(v___x_2097_);
v___x_2099_ = l_Lean_MessageData_joinSep(v___x_2098_, v___x_2091_);
if (v_isShared_2076_ == 0)
{
lean_ctor_set_tag(v___x_2075_, 7);
lean_ctor_set(v___x_2075_, 1, v___x_2099_);
lean_ctor_set(v___x_2075_, 0, v___x_2091_);
v___x_2101_ = v___x_2075_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2091_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v___x_2099_);
v___x_2101_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
v___y_2060_ = v___y_2083_;
v___y_2061_ = v___y_2085_;
v___y_2062_ = v___x_2088_;
v___y_2063_ = v___x_2101_;
goto v___jp_2059_;
}
}
}
}
v___jp_2104_:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2106_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2);
v___x_2107_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
lean_inc(v_fst_2073_);
v___x_2108_ = l_Lean_MessageData_ofName(v_fst_2073_);
v___x_2109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2107_);
lean_ctor_set(v___x_2109_, 1, v___x_2108_);
v___x_2110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2109_);
lean_ctor_set(v___x_2110_, 1, v___x_2107_);
v___x_2111_ = 1;
v___x_2112_ = l_Lean_Name_toString(v_fst_2073_, v___x_2111_);
v___x_2113_ = lean_string_dec_eq(v___x_2112_, v_fst_2077_);
lean_dec_ref(v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2114_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4);
v___x_2115_ = l_Lean_stringToMessageData(v_fst_2077_);
v___x_2116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2114_);
lean_ctor_set(v___x_2116_, 1, v___x_2115_);
v___x_2117_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6);
v___x_2118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2116_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
v___y_2083_ = v_a_2105_;
v___y_2084_ = v___x_2110_;
v___y_2085_ = v___x_2106_;
v___y_2086_ = v___x_2118_;
goto v___jp_2082_;
}
else
{
lean_object* v___x_2119_; 
lean_dec(v_fst_2077_);
v___x_2119_ = l_Lean_MessageData_nil;
v___y_2083_ = v_a_2105_;
v___y_2084_ = v___x_2110_;
v___y_2085_ = v___x_2106_;
v___y_2086_ = v___x_2119_;
goto v___jp_2082_;
}
}
v___jp_2120_:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2122_ = lean_array_to_list(v___y_2121_);
v___x_2123_ = lean_box(0);
v___x_2124_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_2045_, v___x_2122_, v___x_2123_, v___y_2049_, v___y_2050_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2125_);
lean_dec_ref_known(v___x_2124_, 1);
v___x_2126_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2127_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9);
v___x_2128_ = l_Lean_MessageData_joinSep(v_a_2125_, v___x_2127_);
v___x_2129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2126_);
lean_ctor_set(v___x_2129_, 1, v___x_2128_);
v_a_2105_ = v___x_2129_;
goto v___jp_2104_;
}
else
{
lean_del_object(v___x_2080_);
lean_dec(v_snd_2078_);
lean_dec(v_fst_2077_);
lean_del_object(v___x_2075_);
lean_dec(v_fst_2073_);
lean_del_object(v___x_2057_);
lean_dec(v_tail_2055_);
lean_dec(v_x_2048_);
return v___x_2124_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___boxed(lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_x_2155_, lean_object* v_x_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_2153_, v_a_2154_, v_x_2155_, v_x_2156_, v___y_2157_, v___y_2158_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v_a_2154_);
lean_dec(v_a_2153_);
return v_res_2160_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(uint8_t v___y_2162_, uint8_t v_suppressElabErrors_2163_, lean_object* v_x_2164_){
_start:
{
if (lean_obj_tag(v_x_2164_) == 1)
{
lean_object* v_pre_2165_; 
v_pre_2165_ = lean_ctor_get(v_x_2164_, 0);
if (lean_obj_tag(v_pre_2165_) == 0)
{
lean_object* v_str_2166_; lean_object* v___x_2167_; uint8_t v___x_2168_; 
v_str_2166_ = lean_ctor_get(v_x_2164_, 1);
v___x_2167_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___closed__0));
v___x_2168_ = lean_string_dec_eq(v_str_2166_, v___x_2167_);
if (v___x_2168_ == 0)
{
return v___y_2162_;
}
else
{
return v_suppressElabErrors_2163_;
}
}
else
{
return v___y_2162_;
}
}
else
{
return v___y_2162_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed(lean_object* v___y_2169_, lean_object* v_suppressElabErrors_2170_, lean_object* v_x_2171_){
_start:
{
uint8_t v___y_18016__boxed_2172_; uint8_t v_suppressElabErrors_boxed_2173_; uint8_t v_res_2174_; lean_object* v_r_2175_; 
v___y_18016__boxed_2172_ = lean_unbox(v___y_2169_);
v_suppressElabErrors_boxed_2173_ = lean_unbox(v_suppressElabErrors_2170_);
v_res_2174_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0(v___y_18016__boxed_2172_, v_suppressElabErrors_boxed_2173_, v_x_2171_);
lean_dec(v_x_2171_);
v_r_2175_ = lean_box(v_res_2174_);
return v_r_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(lean_object* v_ref_2176_, lean_object* v_msgData_2177_, uint8_t v_severity_2178_, uint8_t v_isSilent_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v___y_2184_; lean_object* v___y_2185_; uint8_t v___y_2186_; lean_object* v___y_2187_; uint8_t v___y_2188_; lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___y_2191_; uint8_t v___y_2247_; uint8_t v___y_2248_; uint8_t v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; uint8_t v___y_2275_; lean_object* v___y_2276_; uint8_t v___y_2277_; uint8_t v___y_2278_; lean_object* v___y_2279_; uint8_t v___y_2283_; uint8_t v___y_2284_; uint8_t v___y_2285_; uint8_t v___x_2300_; uint8_t v___y_2302_; uint8_t v___y_2303_; uint8_t v___y_2304_; uint8_t v___y_2306_; uint8_t v___x_2318_; 
v___x_2300_ = 2;
v___x_2318_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2178_, v___x_2300_);
if (v___x_2318_ == 0)
{
v___y_2306_ = v___x_2318_;
goto v___jp_2305_;
}
else
{
uint8_t v___x_2319_; 
lean_inc_ref(v_msgData_2177_);
v___x_2319_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2177_);
v___y_2306_ = v___x_2319_;
goto v___jp_2305_;
}
v___jp_2183_:
{
lean_object* v___x_2192_; 
v___x_2192_ = l_Lean_Elab_Command_getScope___redArg(v___y_2191_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v_a_2193_; lean_object* v___x_2194_; 
v_a_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_a_2193_);
lean_dec_ref_known(v___x_2192_, 1);
v___x_2194_ = l_Lean_Elab_Command_getScope___redArg(v___y_2191_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2229_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2197_ = v___x_2194_;
v_isShared_2198_ = v_isSharedCheck_2229_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_a_2195_);
lean_dec(v___x_2194_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2229_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2199_; lean_object* v_currNamespace_2200_; lean_object* v_openDecls_2201_; lean_object* v_env_2202_; lean_object* v_messages_2203_; lean_object* v_scopes_2204_; lean_object* v_usedQuotCtxts_2205_; lean_object* v_nextMacroScope_2206_; lean_object* v_maxRecDepth_2207_; lean_object* v_ngen_2208_; lean_object* v_auxDeclNGen_2209_; lean_object* v_infoState_2210_; lean_object* v_traceState_2211_; lean_object* v_snapshotTasks_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2228_; 
v___x_2199_ = lean_st_ref_take(v___y_2191_);
v_currNamespace_2200_ = lean_ctor_get(v_a_2193_, 2);
lean_inc(v_currNamespace_2200_);
lean_dec(v_a_2193_);
v_openDecls_2201_ = lean_ctor_get(v_a_2195_, 3);
lean_inc(v_openDecls_2201_);
lean_dec(v_a_2195_);
v_env_2202_ = lean_ctor_get(v___x_2199_, 0);
v_messages_2203_ = lean_ctor_get(v___x_2199_, 1);
v_scopes_2204_ = lean_ctor_get(v___x_2199_, 2);
v_usedQuotCtxts_2205_ = lean_ctor_get(v___x_2199_, 3);
v_nextMacroScope_2206_ = lean_ctor_get(v___x_2199_, 4);
v_maxRecDepth_2207_ = lean_ctor_get(v___x_2199_, 5);
v_ngen_2208_ = lean_ctor_get(v___x_2199_, 6);
v_auxDeclNGen_2209_ = lean_ctor_get(v___x_2199_, 7);
v_infoState_2210_ = lean_ctor_get(v___x_2199_, 8);
v_traceState_2211_ = lean_ctor_get(v___x_2199_, 9);
v_snapshotTasks_2212_ = lean_ctor_get(v___x_2199_, 10);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2214_ = v___x_2199_;
v_isShared_2215_ = v_isSharedCheck_2228_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_snapshotTasks_2212_);
lean_inc(v_traceState_2211_);
lean_inc(v_infoState_2210_);
lean_inc(v_auxDeclNGen_2209_);
lean_inc(v_ngen_2208_);
lean_inc(v_maxRecDepth_2207_);
lean_inc(v_nextMacroScope_2206_);
lean_inc(v_usedQuotCtxts_2205_);
lean_inc(v_scopes_2204_);
lean_inc(v_messages_2203_);
lean_inc(v_env_2202_);
lean_dec(v___x_2199_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2228_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2221_; 
v___x_2216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2216_, 0, v_currNamespace_2200_);
lean_ctor_set(v___x_2216_, 1, v_openDecls_2201_);
v___x_2217_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2216_);
lean_ctor_set(v___x_2217_, 1, v___y_2185_);
lean_inc_ref(v___y_2184_);
lean_inc_ref(v___y_2187_);
v___x_2218_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2218_, 0, v___y_2187_);
lean_ctor_set(v___x_2218_, 1, v___y_2190_);
lean_ctor_set(v___x_2218_, 2, v___y_2189_);
lean_ctor_set(v___x_2218_, 3, v___y_2184_);
lean_ctor_set(v___x_2218_, 4, v___x_2217_);
lean_ctor_set_uint8(v___x_2218_, sizeof(void*)*5, v___y_2186_);
lean_ctor_set_uint8(v___x_2218_, sizeof(void*)*5 + 1, v___y_2188_);
lean_ctor_set_uint8(v___x_2218_, sizeof(void*)*5 + 2, v_isSilent_2179_);
v___x_2219_ = l_Lean_MessageLog_add(v___x_2218_, v_messages_2203_);
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 1, v___x_2219_);
v___x_2221_ = v___x_2214_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_env_2202_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v___x_2219_);
lean_ctor_set(v_reuseFailAlloc_2227_, 2, v_scopes_2204_);
lean_ctor_set(v_reuseFailAlloc_2227_, 3, v_usedQuotCtxts_2205_);
lean_ctor_set(v_reuseFailAlloc_2227_, 4, v_nextMacroScope_2206_);
lean_ctor_set(v_reuseFailAlloc_2227_, 5, v_maxRecDepth_2207_);
lean_ctor_set(v_reuseFailAlloc_2227_, 6, v_ngen_2208_);
lean_ctor_set(v_reuseFailAlloc_2227_, 7, v_auxDeclNGen_2209_);
lean_ctor_set(v_reuseFailAlloc_2227_, 8, v_infoState_2210_);
lean_ctor_set(v_reuseFailAlloc_2227_, 9, v_traceState_2211_);
lean_ctor_set(v_reuseFailAlloc_2227_, 10, v_snapshotTasks_2212_);
v___x_2221_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2225_; 
v___x_2222_ = lean_st_ref_set(v___y_2191_, v___x_2221_);
v___x_2223_ = lean_box(0);
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 0, v___x_2223_);
v___x_2225_ = v___x_2197_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2223_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
lean_dec(v_a_2193_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2185_);
v_a_2230_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2194_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2194_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2185_);
v_a_2238_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2192_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2192_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
v___jp_2246_:
{
lean_object* v_fileName_2252_; lean_object* v_fileMap_2253_; uint8_t v_suppressElabErrors_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2273_; 
v_fileName_2252_ = lean_ctor_get(v___y_2180_, 0);
v_fileMap_2253_ = lean_ctor_get(v___y_2180_, 1);
v_suppressElabErrors_2254_ = lean_ctor_get_uint8(v___y_2180_, sizeof(void*)*10);
v___x_2255_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2177_);
v___x_2256_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v___x_2255_, v___y_2181_);
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2259_ = v___x_2256_;
v_isShared_2260_ = v_isSharedCheck_2273_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2256_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2273_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
lean_inc_ref_n(v_fileMap_2253_, 2);
v___x_2261_ = l_Lean_FileMap_toPosition(v_fileMap_2253_, v___y_2250_);
lean_dec(v___y_2250_);
v___x_2262_ = l_Lean_FileMap_toPosition(v_fileMap_2253_, v___y_2251_);
lean_dec(v___y_2251_);
v___x_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
v___x_2264_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0));
if (v_suppressElabErrors_2254_ == 0)
{
lean_del_object(v___x_2259_);
v___y_2184_ = v___x_2264_;
v___y_2185_ = v_a_2257_;
v___y_2186_ = v___y_2248_;
v___y_2187_ = v_fileName_2252_;
v___y_2188_ = v___y_2249_;
v___y_2189_ = v___x_2263_;
v___y_2190_ = v___x_2261_;
v___y_2191_ = v___y_2181_;
goto v___jp_2183_;
}
else
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___f_2267_; uint8_t v___x_2268_; 
v___x_2265_ = lean_box(v___y_2247_);
v___x_2266_ = lean_box(v_suppressElabErrors_2254_);
v___f_2267_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2267_, 0, v___x_2265_);
lean_closure_set(v___f_2267_, 1, v___x_2266_);
lean_inc(v_a_2257_);
v___x_2268_ = l_Lean_MessageData_hasTag(v___f_2267_, v_a_2257_);
if (v___x_2268_ == 0)
{
lean_object* v___x_2269_; lean_object* v___x_2271_; 
lean_dec_ref_known(v___x_2263_, 1);
lean_dec_ref(v___x_2261_);
lean_dec(v_a_2257_);
v___x_2269_ = lean_box(0);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v___x_2269_);
v___x_2271_ = v___x_2259_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v___x_2269_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
else
{
lean_del_object(v___x_2259_);
v___y_2184_ = v___x_2264_;
v___y_2185_ = v_a_2257_;
v___y_2186_ = v___y_2248_;
v___y_2187_ = v_fileName_2252_;
v___y_2188_ = v___y_2249_;
v___y_2189_ = v___x_2263_;
v___y_2190_ = v___x_2261_;
v___y_2191_ = v___y_2181_;
goto v___jp_2183_;
}
}
}
}
v___jp_2274_:
{
lean_object* v___x_2280_; 
v___x_2280_ = l_Lean_Syntax_getTailPos_x3f(v___y_2276_, v___y_2277_);
lean_dec(v___y_2276_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_inc(v___y_2279_);
v___y_2247_ = v___y_2275_;
v___y_2248_ = v___y_2277_;
v___y_2249_ = v___y_2278_;
v___y_2250_ = v___y_2279_;
v___y_2251_ = v___y_2279_;
goto v___jp_2246_;
}
else
{
lean_object* v_val_2281_; 
v_val_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_val_2281_);
lean_dec_ref_known(v___x_2280_, 1);
v___y_2247_ = v___y_2275_;
v___y_2248_ = v___y_2277_;
v___y_2249_ = v___y_2278_;
v___y_2250_ = v___y_2279_;
v___y_2251_ = v_val_2281_;
goto v___jp_2246_;
}
}
v___jp_2282_:
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Lean_Elab_Command_getRef___redArg(v___y_2180_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; lean_object* v_ref_2288_; lean_object* v___x_2289_; 
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_a_2287_);
lean_dec_ref_known(v___x_2286_, 1);
v_ref_2288_ = l_Lean_replaceRef(v_ref_2176_, v_a_2287_);
lean_dec(v_a_2287_);
v___x_2289_ = l_Lean_Syntax_getPos_x3f(v_ref_2288_, v___y_2284_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v___x_2290_; 
v___x_2290_ = lean_unsigned_to_nat(0u);
v___y_2275_ = v___y_2283_;
v___y_2276_ = v_ref_2288_;
v___y_2277_ = v___y_2284_;
v___y_2278_ = v___y_2285_;
v___y_2279_ = v___x_2290_;
goto v___jp_2274_;
}
else
{
lean_object* v_val_2291_; 
v_val_2291_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_val_2291_);
lean_dec_ref_known(v___x_2289_, 1);
v___y_2275_ = v___y_2283_;
v___y_2276_ = v_ref_2288_;
v___y_2277_ = v___y_2284_;
v___y_2278_ = v___y_2285_;
v___y_2279_ = v_val_2291_;
goto v___jp_2274_;
}
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
lean_dec_ref(v_msgData_2177_);
v_a_2292_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2286_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2286_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
v___jp_2301_:
{
if (v___y_2304_ == 0)
{
v___y_2283_ = v___y_2302_;
v___y_2284_ = v___y_2303_;
v___y_2285_ = v_severity_2178_;
goto v___jp_2282_;
}
else
{
v___y_2283_ = v___y_2302_;
v___y_2284_ = v___y_2303_;
v___y_2285_ = v___x_2300_;
goto v___jp_2282_;
}
}
v___jp_2305_:
{
if (v___y_2306_ == 0)
{
lean_object* v___x_2307_; lean_object* v_scopes_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v_opts_2311_; uint8_t v___x_2312_; uint8_t v___x_2313_; 
v___x_2307_ = lean_st_ref_get(v___y_2181_);
v_scopes_2308_ = lean_ctor_get(v___x_2307_, 2);
lean_inc(v_scopes_2308_);
lean_dec(v___x_2307_);
v___x_2309_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2310_ = l_List_head_x21___redArg(v___x_2309_, v_scopes_2308_);
lean_dec(v_scopes_2308_);
v_opts_2311_ = lean_ctor_get(v___x_2310_, 1);
lean_inc_ref(v_opts_2311_);
lean_dec(v___x_2310_);
v___x_2312_ = 1;
v___x_2313_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2178_, v___x_2312_);
if (v___x_2313_ == 0)
{
lean_dec_ref(v_opts_2311_);
v___y_2302_ = v___y_2306_;
v___y_2303_ = v___y_2306_;
v___y_2304_ = v___x_2313_;
goto v___jp_2301_;
}
else
{
lean_object* v___x_2314_; uint8_t v___x_2315_; 
v___x_2314_ = l_Lean_warningAsError;
v___x_2315_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(v_opts_2311_, v___x_2314_);
lean_dec_ref(v_opts_2311_);
v___y_2302_ = v___y_2306_;
v___y_2303_ = v___y_2306_;
v___y_2304_ = v___x_2315_;
goto v___jp_2301_;
}
}
else
{
lean_object* v___x_2316_; lean_object* v___x_2317_; 
lean_dec_ref(v_msgData_2177_);
v___x_2316_ = lean_box(0);
v___x_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2316_);
return v___x_2317_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32___boxed(lean_object* v_ref_2320_, lean_object* v_msgData_2321_, lean_object* v_severity_2322_, lean_object* v_isSilent_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
uint8_t v_severity_boxed_2327_; uint8_t v_isSilent_boxed_2328_; lean_object* v_res_2329_; 
v_severity_boxed_2327_ = lean_unbox(v_severity_2322_);
v_isSilent_boxed_2328_ = lean_unbox(v_isSilent_2323_);
v_res_2329_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_ref_2320_, v_msgData_2321_, v_severity_boxed_2327_, v_isSilent_boxed_2328_, v___y_2324_, v___y_2325_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v_ref_2320_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(lean_object* v_msgData_2330_, uint8_t v_severity_2331_, uint8_t v_isSilent_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v___x_2336_; 
v___x_2336_ = l_Lean_Elab_Command_getRef___redArg(v___y_2333_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; lean_object* v___x_2338_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2336_, 1);
v___x_2338_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26_spec__32(v_a_2337_, v_msgData_2330_, v_severity_2331_, v_isSilent_2332_, v___y_2333_, v___y_2334_);
lean_dec(v_a_2337_);
return v___x_2338_;
}
else
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2346_; 
lean_dec_ref(v_msgData_2330_);
v_a_2339_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2341_ = v___x_2336_;
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2336_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2344_; 
if (v_isShared_2342_ == 0)
{
v___x_2344_ = v___x_2341_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2339_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26___boxed(lean_object* v_msgData_2347_, lean_object* v_severity_2348_, lean_object* v_isSilent_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
uint8_t v_severity_boxed_2353_; uint8_t v_isSilent_boxed_2354_; lean_object* v_res_2355_; 
v_severity_boxed_2353_ = lean_unbox(v_severity_2348_);
v_isSilent_boxed_2354_ = lean_unbox(v_isSilent_2349_);
v_res_2355_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_2347_, v_severity_boxed_2353_, v_isSilent_boxed_2354_, v___y_2350_, v___y_2351_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(lean_object* v_msgData_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
uint8_t v___x_2360_; uint8_t v___x_2361_; lean_object* v___x_2362_; 
v___x_2360_ = 0;
v___x_2361_ = 0;
v___x_2362_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__26(v_msgData_2356_, v___x_2360_, v___x_2361_, v___y_2357_, v___y_2358_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12___boxed(lean_object* v_msgData_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v_msgData_2363_, v___y_2364_, v___y_2365_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(lean_object* v_init_2368_, lean_object* v_x_2369_){
_start:
{
if (lean_obj_tag(v_x_2369_) == 0)
{
lean_object* v_k_2371_; lean_object* v_v_2372_; lean_object* v_l_2373_; lean_object* v_r_2374_; lean_object* v___x_2375_; lean_object* v_a_2376_; lean_object* v_a_2377_; lean_object* v___x_2378_; 
v_k_2371_ = lean_ctor_get(v_x_2369_, 1);
lean_inc(v_k_2371_);
v_v_2372_ = lean_ctor_get(v_x_2369_, 2);
lean_inc(v_v_2372_);
v_l_2373_ = lean_ctor_get(v_x_2369_, 3);
lean_inc(v_l_2373_);
v_r_2374_ = lean_ctor_get(v_x_2369_, 4);
lean_inc(v_r_2374_);
lean_dec_ref_known(v_x_2369_, 5);
v___x_2375_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_2368_, v_l_2373_);
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
lean_inc(v_a_2376_);
lean_dec_ref(v___x_2375_);
v_a_2377_ = lean_ctor_get(v_a_2376_, 0);
lean_inc(v_a_2377_);
lean_dec(v_a_2376_);
v___x_2378_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2371_, v_v_2372_, v_a_2377_);
v_init_2368_ = v___x_2378_;
v_x_2369_ = v_r_2374_;
goto _start;
}
else
{
lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2380_, 0, v_init_2368_);
v___x_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
return v___x_2381_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___boxed(lean_object* v_init_2382_, lean_object* v_x_2383_, lean_object* v___y_2384_){
_start:
{
lean_object* v_res_2385_; 
v_res_2385_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_2382_, v_x_2383_);
return v_res_2385_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(uint8_t v___x_2386_, lean_object* v_x1_2387_, lean_object* v_x2_2388_){
_start:
{
lean_object* v_fst_2389_; lean_object* v_fst_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; uint8_t v___x_2393_; 
v_fst_2389_ = lean_ctor_get(v_x1_2387_, 0);
lean_inc(v_fst_2389_);
lean_dec_ref(v_x1_2387_);
v_fst_2390_ = lean_ctor_get(v_x2_2388_, 0);
lean_inc(v_fst_2390_);
lean_dec_ref(v_x2_2388_);
v___x_2391_ = l_Lean_Name_toString(v_fst_2389_, v___x_2386_);
v___x_2392_ = l_Lean_Name_toString(v_fst_2390_, v___x_2386_);
v___x_2393_ = lean_string_dec_lt(v___x_2391_, v___x_2392_);
lean_dec_ref(v___x_2392_);
lean_dec_ref(v___x_2391_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0___boxed(lean_object* v___x_2394_, lean_object* v_x1_2395_, lean_object* v_x2_2396_){
_start:
{
uint8_t v___x_18359__boxed_2397_; uint8_t v_res_2398_; lean_object* v_r_2399_; 
v___x_18359__boxed_2397_ = lean_unbox(v___x_2394_);
v_res_2398_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_18359__boxed_2397_, v_x1_2395_, v_x2_2396_);
v_r_2399_ = lean_box(v_res_2398_);
return v_r_2399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(lean_object* v_hi_2400_, lean_object* v_pivot_2401_, lean_object* v_as_2402_, lean_object* v_i_2403_, lean_object* v_k_2404_){
_start:
{
uint8_t v___x_2405_; 
v___x_2405_ = lean_nat_dec_lt(v_k_2404_, v_hi_2400_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2406_; lean_object* v___x_2407_; 
lean_dec(v_k_2404_);
lean_dec_ref(v_pivot_2401_);
v___x_2406_ = lean_array_fswap(v_as_2402_, v_i_2403_, v_hi_2400_);
v___x_2407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2407_, 0, v_i_2403_);
lean_ctor_set(v___x_2407_, 1, v___x_2406_);
return v___x_2407_;
}
else
{
lean_object* v___x_2408_; lean_object* v_fst_2409_; lean_object* v_fst_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; uint8_t v___x_2413_; 
v___x_2408_ = lean_array_fget_borrowed(v_as_2402_, v_k_2404_);
v_fst_2409_ = lean_ctor_get(v___x_2408_, 0);
v_fst_2410_ = lean_ctor_get(v_pivot_2401_, 0);
lean_inc(v_fst_2409_);
v___x_2411_ = l_Lean_Name_toString(v_fst_2409_, v___x_2405_);
lean_inc(v_fst_2410_);
v___x_2412_ = l_Lean_Name_toString(v_fst_2410_, v___x_2405_);
v___x_2413_ = lean_string_dec_lt(v___x_2411_, v___x_2412_);
lean_dec_ref(v___x_2412_);
lean_dec_ref(v___x_2411_);
if (v___x_2413_ == 0)
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2414_ = lean_unsigned_to_nat(1u);
v___x_2415_ = lean_nat_add(v_k_2404_, v___x_2414_);
lean_dec(v_k_2404_);
v_k_2404_ = v___x_2415_;
goto _start;
}
else
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2417_ = lean_array_fswap(v_as_2402_, v_i_2403_, v_k_2404_);
v___x_2418_ = lean_unsigned_to_nat(1u);
v___x_2419_ = lean_nat_add(v_i_2403_, v___x_2418_);
lean_dec(v_i_2403_);
v___x_2420_ = lean_nat_add(v_k_2404_, v___x_2418_);
lean_dec(v_k_2404_);
v_as_2402_ = v___x_2417_;
v_i_2403_ = v___x_2419_;
v_k_2404_ = v___x_2420_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg___boxed(lean_object* v_hi_2422_, lean_object* v_pivot_2423_, lean_object* v_as_2424_, lean_object* v_i_2425_, lean_object* v_k_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_2422_, v_pivot_2423_, v_as_2424_, v_i_2425_, v_k_2426_);
lean_dec(v_hi_2422_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(lean_object* v_n_2428_, lean_object* v_as_2429_, lean_object* v_lo_2430_, lean_object* v_hi_2431_){
_start:
{
lean_object* v___y_2433_; uint8_t v___x_2443_; 
v___x_2443_ = lean_nat_dec_lt(v_lo_2430_, v_hi_2431_);
if (v___x_2443_ == 0)
{
lean_dec(v_lo_2430_);
return v_as_2429_;
}
else
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v_mid_2446_; lean_object* v___y_2448_; lean_object* v___y_2454_; lean_object* v___x_2459_; lean_object* v___x_2460_; uint8_t v___x_2461_; 
v___x_2444_ = lean_nat_add(v_lo_2430_, v_hi_2431_);
v___x_2445_ = lean_unsigned_to_nat(1u);
v_mid_2446_ = lean_nat_shiftr(v___x_2444_, v___x_2445_);
lean_dec(v___x_2444_);
v___x_2459_ = lean_array_fget_borrowed(v_as_2429_, v_mid_2446_);
v___x_2460_ = lean_array_fget_borrowed(v_as_2429_, v_lo_2430_);
lean_inc(v___x_2460_);
lean_inc(v___x_2459_);
v___x_2461_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_2443_, v___x_2459_, v___x_2460_);
if (v___x_2461_ == 0)
{
v___y_2454_ = v_as_2429_;
goto v___jp_2453_;
}
else
{
lean_object* v___x_2462_; 
v___x_2462_ = lean_array_fswap(v_as_2429_, v_lo_2430_, v_mid_2446_);
v___y_2454_ = v___x_2462_;
goto v___jp_2453_;
}
v___jp_2447_:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; uint8_t v___x_2451_; 
v___x_2449_ = lean_array_fget_borrowed(v___y_2448_, v_mid_2446_);
v___x_2450_ = lean_array_fget_borrowed(v___y_2448_, v_hi_2431_);
lean_inc(v___x_2450_);
lean_inc(v___x_2449_);
v___x_2451_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_2443_, v___x_2449_, v___x_2450_);
if (v___x_2451_ == 0)
{
lean_dec(v_mid_2446_);
v___y_2433_ = v___y_2448_;
goto v___jp_2432_;
}
else
{
lean_object* v___x_2452_; 
v___x_2452_ = lean_array_fswap(v___y_2448_, v_mid_2446_, v_hi_2431_);
lean_dec(v_mid_2446_);
v___y_2433_ = v___x_2452_;
goto v___jp_2432_;
}
}
v___jp_2453_:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; uint8_t v___x_2457_; 
v___x_2455_ = lean_array_fget_borrowed(v___y_2454_, v_hi_2431_);
v___x_2456_ = lean_array_fget_borrowed(v___y_2454_, v_lo_2430_);
lean_inc(v___x_2456_);
lean_inc(v___x_2455_);
v___x_2457_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___lam__0(v___x_2443_, v___x_2455_, v___x_2456_);
if (v___x_2457_ == 0)
{
v___y_2448_ = v___y_2454_;
goto v___jp_2447_;
}
else
{
lean_object* v___x_2458_; 
v___x_2458_ = lean_array_fswap(v___y_2454_, v_lo_2430_, v_hi_2431_);
v___y_2448_ = v___x_2458_;
goto v___jp_2447_;
}
}
}
v___jp_2432_:
{
lean_object* v_pivot_2434_; lean_object* v___x_2435_; lean_object* v_fst_2436_; lean_object* v_snd_2437_; uint8_t v___x_2438_; 
v_pivot_2434_ = lean_array_fget(v___y_2433_, v_hi_2431_);
lean_inc_n(v_lo_2430_, 2);
v___x_2435_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_2431_, v_pivot_2434_, v___y_2433_, v_lo_2430_, v_lo_2430_);
v_fst_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_fst_2436_);
v_snd_2437_ = lean_ctor_get(v___x_2435_, 1);
lean_inc(v_snd_2437_);
lean_dec_ref(v___x_2435_);
v___x_2438_ = lean_nat_dec_le(v_hi_2431_, v_fst_2436_);
if (v___x_2438_ == 0)
{
lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2439_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_2428_, v_snd_2437_, v_lo_2430_, v_fst_2436_);
v___x_2440_ = lean_unsigned_to_nat(1u);
v___x_2441_ = lean_nat_add(v_fst_2436_, v___x_2440_);
lean_dec(v_fst_2436_);
v_as_2429_ = v___x_2439_;
v_lo_2430_ = v___x_2441_;
goto _start;
}
else
{
lean_dec(v_fst_2436_);
lean_dec(v_lo_2430_);
return v_snd_2437_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg___boxed(lean_object* v_n_2463_, lean_object* v_as_2464_, lean_object* v_lo_2465_, lean_object* v_hi_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_2463_, v_as_2464_, v_lo_2465_, v_hi_2466_);
lean_dec(v_hi_2466_);
lean_dec(v_n_2463_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(lean_object* v_init_2468_, lean_object* v_x_2469_){
_start:
{
if (lean_obj_tag(v_x_2469_) == 0)
{
lean_object* v_k_2470_; lean_object* v_v_2471_; lean_object* v_l_2472_; lean_object* v_r_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v_k_2470_ = lean_ctor_get(v_x_2469_, 1);
v_v_2471_ = lean_ctor_get(v_x_2469_, 2);
v_l_2472_ = lean_ctor_get(v_x_2469_, 3);
v_r_2473_ = lean_ctor_get(v_x_2469_, 4);
v___x_2474_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_2468_, v_l_2472_);
lean_inc(v_v_2471_);
lean_inc(v_k_2470_);
v___x_2475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2475_, 0, v_k_2470_);
lean_ctor_set(v___x_2475_, 1, v_v_2471_);
v___x_2476_ = lean_array_push(v___x_2474_, v___x_2475_);
v_init_2468_ = v___x_2476_;
v_x_2469_ = v_r_2473_;
goto _start;
}
else
{
return v_init_2468_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25___boxed(lean_object* v_init_2478_, lean_object* v_x_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_2478_, v_x_2479_);
lean_dec(v_x_2479_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(lean_object* v_as_2481_, size_t v_sz_2482_, size_t v_i_2483_, lean_object* v_b_2484_){
_start:
{
uint8_t v___x_2486_; 
v___x_2486_ = lean_usize_dec_lt(v_i_2483_, v_sz_2482_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; 
v___x_2487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2487_, 0, v_b_2484_);
return v___x_2487_;
}
else
{
lean_object* v_a_2488_; lean_object* v_fst_2489_; lean_object* v_snd_2490_; lean_object* v_found_2491_; size_t v___x_2492_; size_t v___x_2493_; 
v_a_2488_ = lean_array_uget_borrowed(v_as_2481_, v_i_2483_);
v_fst_2489_ = lean_ctor_get(v_a_2488_, 0);
v_snd_2490_ = lean_ctor_get(v_a_2488_, 1);
lean_inc(v_snd_2490_);
lean_inc(v_fst_2489_);
v_found_2491_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2489_, v_snd_2490_, v_b_2484_);
v___x_2492_ = ((size_t)1ULL);
v___x_2493_ = lean_usize_add(v_i_2483_, v___x_2492_);
v_i_2483_ = v___x_2493_;
v_b_2484_ = v_found_2491_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg___boxed(lean_object* v_as_2495_, lean_object* v_sz_2496_, lean_object* v_i_2497_, lean_object* v_b_2498_, lean_object* v___y_2499_){
_start:
{
size_t v_sz_boxed_2500_; size_t v_i_boxed_2501_; lean_object* v_res_2502_; 
v_sz_boxed_2500_ = lean_unbox_usize(v_sz_2496_);
lean_dec(v_sz_2496_);
v_i_boxed_2501_ = lean_unbox_usize(v_i_2497_);
lean_dec(v_i_2497_);
v_res_2502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_2495_, v_sz_boxed_2500_, v_i_boxed_2501_, v_b_2498_);
lean_dec_ref(v_as_2495_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(lean_object* v_as_2503_, size_t v_sz_2504_, size_t v_i_2505_, lean_object* v_b_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
uint8_t v___x_2510_; 
v___x_2510_ = lean_usize_dec_lt(v_i_2505_, v_sz_2504_);
if (v___x_2510_ == 0)
{
lean_object* v___x_2511_; 
v___x_2511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2511_, 0, v_b_2506_);
return v___x_2511_;
}
else
{
lean_object* v_a_2512_; size_t v_sz_2513_; size_t v___x_2514_; lean_object* v___x_2515_; 
v_a_2512_ = lean_array_uget_borrowed(v_as_2503_, v_i_2505_);
v_sz_2513_ = lean_array_size(v_a_2512_);
v___x_2514_ = ((size_t)0ULL);
v___x_2515_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_a_2512_, v_sz_2513_, v___x_2514_, v_b_2506_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; size_t v___x_2517_; size_t v___x_2518_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_a_2516_);
lean_dec_ref_known(v___x_2515_, 1);
v___x_2517_ = ((size_t)1ULL);
v___x_2518_ = lean_usize_add(v_i_2505_, v___x_2517_);
v_i_2505_ = v___x_2518_;
v_b_2506_ = v_a_2516_;
goto _start;
}
else
{
return v___x_2515_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___boxed(lean_object* v_as_2520_, lean_object* v_sz_2521_, lean_object* v_i_2522_, lean_object* v_b_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_){
_start:
{
size_t v_sz_boxed_2527_; size_t v_i_boxed_2528_; lean_object* v_res_2529_; 
v_sz_boxed_2527_ = lean_unbox_usize(v_sz_2521_);
lean_dec(v_sz_2521_);
v_i_boxed_2528_ = lean_unbox_usize(v_i_2522_);
lean_dec(v_i_2522_);
v_res_2529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_as_2520_, v_sz_boxed_2527_, v_i_boxed_2528_, v_b_2523_, v___y_2524_, v___y_2525_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec_ref(v_as_2520_);
return v_res_2529_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2530_ = lean_box(1);
v___x_2531_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2530_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v___y_2538_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___x_2553_; lean_object* v_env_2554_; lean_object* v___x_2555_; lean_object* v_toEnvExtension_2556_; lean_object* v_asyncMode_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v_a_2563_; lean_object* v_a_2565_; lean_object* v_a_2588_; 
v___x_2553_ = lean_st_ref_get(v___y_2535_);
v_env_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc_ref_n(v_env_2554_, 2);
lean_dec(v___x_2553_);
v___x_2555_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2556_ = lean_ctor_get(v___x_2555_, 0);
v_asyncMode_2557_ = lean_ctor_get(v_toEnvExtension_2556_, 2);
v___x_2558_ = lean_box(1);
v___x_2559_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0, &l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0_once, _init_l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0);
v___x_2560_ = lean_box(0);
v___x_2561_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2558_, v___x_2555_, v_env_2554_, v_asyncMode_2557_, v___x_2560_);
v___x_2562_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v___x_2558_, v___x_2561_);
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2563_);
lean_dec_ref(v___x_2562_);
v_a_2588_ = lean_ctor_get(v_a_2563_, 0);
lean_inc(v_a_2588_);
lean_dec(v_a_2563_);
v_a_2565_ = v_a_2588_;
goto v___jp_2564_;
v___jp_2537_:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2539_ = lean_array_to_list(v___y_2538_);
v___x_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2540_, 0, v___x_2539_);
return v___x_2540_;
}
v___jp_2541_:
{
lean_object* v___x_2546_; 
v___x_2546_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v___y_2543_, v___y_2542_, v___y_2544_, v___y_2545_);
lean_dec(v___y_2545_);
lean_dec(v___y_2543_);
v___y_2538_ = v___x_2546_;
goto v___jp_2537_;
}
v___jp_2547_:
{
uint8_t v___x_2552_; 
v___x_2552_ = lean_nat_dec_le(v___y_2551_, v___y_2550_);
if (v___x_2552_ == 0)
{
lean_dec(v___y_2550_);
lean_inc(v___y_2551_);
v___y_2542_ = v___y_2548_;
v___y_2543_ = v___y_2549_;
v___y_2544_ = v___y_2551_;
v___y_2545_ = v___y_2551_;
goto v___jp_2541_;
}
else
{
v___y_2542_ = v___y_2548_;
v___y_2543_ = v___y_2549_;
v___y_2544_ = v___y_2551_;
v___y_2545_ = v___y_2550_;
goto v___jp_2541_;
}
}
v___jp_2564_:
{
lean_object* v___x_2566_; lean_object* v_importedEntries_2567_; size_t v_sz_2568_; size_t v___x_2569_; lean_object* v___x_2570_; 
v___x_2566_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2559_, v_toEnvExtension_2556_, v_env_2554_, v_asyncMode_2557_, v___x_2560_);
v_importedEntries_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc_ref(v_importedEntries_2567_);
lean_dec(v___x_2566_);
v_sz_2568_ = lean_array_size(v_importedEntries_2567_);
v___x_2569_ = ((size_t)0ULL);
v___x_2570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_importedEntries_2567_, v_sz_2568_, v___x_2569_, v_a_2565_, v___y_2534_, v___y_2535_);
lean_dec_ref(v_importedEntries_2567_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v_a_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v_arr_2574_; lean_object* v___x_2575_; uint8_t v___x_2576_; 
v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
lean_inc(v_a_2571_);
lean_dec_ref_known(v___x_2570_, 1);
v___x_2572_ = lean_unsigned_to_nat(0u);
v___x_2573_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__1));
v_arr_2574_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v___x_2573_, v_a_2571_);
lean_dec(v_a_2571_);
v___x_2575_ = lean_array_get_size(v_arr_2574_);
v___x_2576_ = lean_nat_dec_eq(v___x_2575_, v___x_2572_);
if (v___x_2576_ == 0)
{
lean_object* v___x_2577_; lean_object* v___x_2578_; uint8_t v___x_2579_; 
v___x_2577_ = lean_unsigned_to_nat(1u);
v___x_2578_ = lean_nat_sub(v___x_2575_, v___x_2577_);
v___x_2579_ = lean_nat_dec_le(v___x_2572_, v___x_2578_);
if (v___x_2579_ == 0)
{
lean_inc(v___x_2578_);
v___y_2548_ = v_arr_2574_;
v___y_2549_ = v___x_2575_;
v___y_2550_ = v___x_2578_;
v___y_2551_ = v___x_2578_;
goto v___jp_2547_;
}
else
{
v___y_2548_ = v_arr_2574_;
v___y_2549_ = v___x_2575_;
v___y_2550_ = v___x_2578_;
v___y_2551_ = v___x_2572_;
goto v___jp_2547_;
}
}
else
{
v___y_2538_ = v_arr_2574_;
goto v___jp_2537_;
}
}
else
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2587_; 
v_a_2580_ = lean_ctor_get(v___x_2570_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2582_ = v___x_2570_;
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2570_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2580_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___boxed(lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v___y_2589_, v___y_2590_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(lean_object* v_t_2593_, lean_object* v_k_2594_, lean_object* v_fallback_2595_){
_start:
{
if (lean_obj_tag(v_t_2593_) == 0)
{
lean_object* v_k_2596_; lean_object* v_v_2597_; lean_object* v_l_2598_; lean_object* v_r_2599_; uint8_t v___x_2600_; 
v_k_2596_ = lean_ctor_get(v_t_2593_, 1);
v_v_2597_ = lean_ctor_get(v_t_2593_, 2);
v_l_2598_ = lean_ctor_get(v_t_2593_, 3);
v_r_2599_ = lean_ctor_get(v_t_2593_, 4);
v___x_2600_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2594_, v_k_2596_);
switch(v___x_2600_)
{
case 0:
{
v_t_2593_ = v_l_2598_;
goto _start;
}
case 1:
{
lean_inc(v_v_2597_);
return v_v_2597_;
}
default: 
{
v_t_2593_ = v_r_2599_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2595_);
return v_fallback_2595_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg___boxed(lean_object* v_t_2603_, lean_object* v_k_2604_, lean_object* v_fallback_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_2603_, v_k_2604_, v_fallback_2605_);
lean_dec(v_fallback_2605_);
lean_dec(v_k_2604_);
lean_dec(v_t_2603_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(lean_object* v_as_2607_, size_t v_sz_2608_, size_t v_i_2609_, lean_object* v_b_2610_){
_start:
{
uint8_t v___x_2612_; 
v___x_2612_ = lean_usize_dec_lt(v_i_2609_, v_sz_2608_);
if (v___x_2612_ == 0)
{
lean_object* v___x_2613_; 
v___x_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2613_, 0, v_b_2610_);
return v___x_2613_;
}
else
{
lean_object* v_a_2614_; lean_object* v_fst_2615_; lean_object* v_snd_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; size_t v___x_2621_; size_t v___x_2622_; 
v_a_2614_ = lean_array_uget_borrowed(v_as_2607_, v_i_2609_);
v_fst_2615_ = lean_ctor_get(v_a_2614_, 0);
v_snd_2616_ = lean_ctor_get(v_a_2614_, 1);
v___x_2617_ = l_Lean_NameSet_empty;
v___x_2618_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_2610_, v_snd_2616_, v___x_2617_);
lean_inc(v_fst_2615_);
v___x_2619_ = l_Lean_NameSet_insert(v___x_2618_, v_fst_2615_);
lean_inc(v_snd_2616_);
v___x_2620_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_snd_2616_, v___x_2619_, v_b_2610_);
v___x_2621_ = ((size_t)1ULL);
v___x_2622_ = lean_usize_add(v_i_2609_, v___x_2621_);
v_i_2609_ = v___x_2622_;
v_b_2610_ = v___x_2620_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg___boxed(lean_object* v_as_2624_, lean_object* v_sz_2625_, lean_object* v_i_2626_, lean_object* v_b_2627_, lean_object* v___y_2628_){
_start:
{
size_t v_sz_boxed_2629_; size_t v_i_boxed_2630_; lean_object* v_res_2631_; 
v_sz_boxed_2629_ = lean_unbox_usize(v_sz_2625_);
lean_dec(v_sz_2625_);
v_i_boxed_2630_ = lean_unbox_usize(v_i_2626_);
lean_dec(v_i_2626_);
v_res_2631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_2624_, v_sz_boxed_2629_, v_i_boxed_2630_, v_b_2627_);
lean_dec_ref(v_as_2624_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(lean_object* v_as_2632_, size_t v_sz_2633_, size_t v_i_2634_, lean_object* v_b_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
uint8_t v___x_2639_; 
v___x_2639_ = lean_usize_dec_lt(v_i_2634_, v_sz_2633_);
if (v___x_2639_ == 0)
{
lean_object* v___x_2640_; 
v___x_2640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2640_, 0, v_b_2635_);
return v___x_2640_;
}
else
{
lean_object* v_a_2641_; size_t v_sz_2642_; size_t v___x_2643_; lean_object* v___x_2644_; 
v_a_2641_ = lean_array_uget_borrowed(v_as_2632_, v_i_2634_);
v_sz_2642_ = lean_array_size(v_a_2641_);
v___x_2643_ = ((size_t)0ULL);
v___x_2644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_a_2641_, v_sz_2642_, v___x_2643_, v_b_2635_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v_a_2645_; size_t v___x_2646_; size_t v___x_2647_; 
v_a_2645_ = lean_ctor_get(v___x_2644_, 0);
lean_inc(v_a_2645_);
lean_dec_ref_known(v___x_2644_, 1);
v___x_2646_ = ((size_t)1ULL);
v___x_2647_ = lean_usize_add(v_i_2634_, v___x_2646_);
v_i_2634_ = v___x_2647_;
v_b_2635_ = v_a_2645_;
goto _start;
}
else
{
return v___x_2644_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2___boxed(lean_object* v_as_2649_, lean_object* v_sz_2650_, lean_object* v_i_2651_, lean_object* v_b_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
size_t v_sz_boxed_2656_; size_t v_i_boxed_2657_; lean_object* v_res_2658_; 
v_sz_boxed_2656_ = lean_unbox_usize(v_sz_2650_);
lean_dec(v_sz_2650_);
v_i_boxed_2657_ = lean_unbox_usize(v_i_2651_);
lean_dec(v_i_2651_);
v_res_2658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v_as_2649_, v_sz_boxed_2656_, v_i_boxed_2657_, v_b_2652_, v___y_2653_, v___y_2654_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec_ref(v_as_2649_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(lean_object* v_as_2659_, size_t v_i_2660_, size_t v_stop_2661_, lean_object* v_b_2662_){
_start:
{
uint8_t v___x_2663_; 
v___x_2663_ = lean_usize_dec_eq(v_i_2660_, v_stop_2661_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2664_; lean_object* v_fst_2665_; lean_object* v_snd_2666_; lean_object* v___x_2667_; size_t v___x_2668_; size_t v___x_2669_; 
v___x_2664_ = lean_array_uget_borrowed(v_as_2659_, v_i_2660_);
v_fst_2665_ = lean_ctor_get(v___x_2664_, 0);
v_snd_2666_ = lean_ctor_get(v___x_2664_, 1);
lean_inc(v_snd_2666_);
lean_inc(v_fst_2665_);
v___x_2667_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2665_, v_snd_2666_, v_b_2662_);
v___x_2668_ = ((size_t)1ULL);
v___x_2669_ = lean_usize_add(v_i_2660_, v___x_2668_);
v_i_2660_ = v___x_2669_;
v_b_2662_ = v___x_2667_;
goto _start;
}
else
{
return v_b_2662_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3___boxed(lean_object* v_as_2671_, lean_object* v_i_2672_, lean_object* v_stop_2673_, lean_object* v_b_2674_){
_start:
{
size_t v_i_boxed_2675_; size_t v_stop_boxed_2676_; lean_object* v_res_2677_; 
v_i_boxed_2675_ = lean_unbox_usize(v_i_2672_);
lean_dec(v_i_2672_);
v_stop_boxed_2676_ = lean_unbox_usize(v_stop_2673_);
lean_dec(v_stop_2673_);
v_res_2677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v_as_2671_, v_i_boxed_2675_, v_stop_boxed_2676_, v_b_2674_);
lean_dec_ref(v_as_2671_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(lean_object* v_as_2678_, size_t v_i_2679_, size_t v_stop_2680_, lean_object* v_b_2681_){
_start:
{
lean_object* v___y_2683_; uint8_t v___x_2687_; 
v___x_2687_ = lean_usize_dec_eq(v_i_2679_, v_stop_2680_);
if (v___x_2687_ == 0)
{
lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; uint8_t v___x_2691_; 
v___x_2688_ = lean_array_uget_borrowed(v_as_2678_, v_i_2679_);
v___x_2689_ = lean_unsigned_to_nat(0u);
v___x_2690_ = lean_array_get_size(v___x_2688_);
v___x_2691_ = lean_nat_dec_lt(v___x_2689_, v___x_2690_);
if (v___x_2691_ == 0)
{
v___y_2683_ = v_b_2681_;
goto v___jp_2682_;
}
else
{
uint8_t v___x_2692_; 
v___x_2692_ = lean_nat_dec_le(v___x_2690_, v___x_2690_);
if (v___x_2692_ == 0)
{
if (v___x_2691_ == 0)
{
v___y_2683_ = v_b_2681_;
goto v___jp_2682_;
}
else
{
size_t v___x_2693_; size_t v___x_2694_; lean_object* v___x_2695_; 
v___x_2693_ = ((size_t)0ULL);
v___x_2694_ = lean_usize_of_nat(v___x_2690_);
v___x_2695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_2688_, v___x_2693_, v___x_2694_, v_b_2681_);
v___y_2683_ = v___x_2695_;
goto v___jp_2682_;
}
}
else
{
size_t v___x_2696_; size_t v___x_2697_; lean_object* v___x_2698_; 
v___x_2696_ = ((size_t)0ULL);
v___x_2697_ = lean_usize_of_nat(v___x_2690_);
v___x_2698_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_2688_, v___x_2696_, v___x_2697_, v_b_2681_);
v___y_2683_ = v___x_2698_;
goto v___jp_2682_;
}
}
}
else
{
return v_b_2681_;
}
v___jp_2682_:
{
size_t v___x_2684_; size_t v___x_2685_; 
v___x_2684_ = ((size_t)1ULL);
v___x_2685_ = lean_usize_add(v_i_2679_, v___x_2684_);
v_i_2679_ = v___x_2685_;
v_b_2681_ = v___y_2683_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5___boxed(lean_object* v_as_2699_, lean_object* v_i_2700_, lean_object* v_stop_2701_, lean_object* v_b_2702_){
_start:
{
size_t v_i_boxed_2703_; size_t v_stop_boxed_2704_; lean_object* v_res_2705_; 
v_i_boxed_2703_ = lean_unbox_usize(v_i_2700_);
lean_dec(v_i_2700_);
v_stop_boxed_2704_ = lean_unbox_usize(v_stop_2701_);
lean_dec(v_stop_2701_);
v_res_2705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v_as_2699_, v_i_boxed_2703_, v_stop_boxed_2704_, v_b_2702_);
lean_dec_ref(v_as_2699_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(lean_object* v___y_2706_){
_start:
{
lean_object* v___x_2708_; lean_object* v_env_2709_; lean_object* v___x_2710_; lean_object* v_ext_2711_; lean_object* v_toEnvExtension_2712_; lean_object* v_asyncMode_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v_categories_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2708_ = lean_st_ref_get(v___y_2706_);
v_env_2709_ = lean_ctor_get(v___x_2708_, 0);
lean_inc_ref_n(v_env_2709_, 2);
lean_dec(v___x_2708_);
v___x_2710_ = l_Lean_Parser_parserExtension;
v_ext_2711_ = lean_ctor_get(v___x_2710_, 1);
v_toEnvExtension_2712_ = lean_ctor_get(v_ext_2711_, 0);
v_asyncMode_2713_ = lean_ctor_get(v_toEnvExtension_2712_, 2);
v___x_2714_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_2715_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2714_, v___x_2710_, v_env_2709_, v_asyncMode_2713_);
v_categories_2716_ = lean_ctor_get(v___x_2715_, 2);
lean_inc_ref(v_categories_2716_);
lean_dec(v___x_2715_);
v___x_2717_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_2718_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_2716_, v___x_2717_);
lean_dec_ref(v_categories_2716_);
if (lean_obj_tag(v___x_2718_) == 1)
{
lean_object* v_val_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2756_; 
v_val_2719_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2721_ = v___x_2718_;
v_isShared_2722_ = v_isSharedCheck_2756_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_val_2719_);
lean_dec(v___x_2718_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2756_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___y_2724_; lean_object* v___x_2733_; lean_object* v_toEnvExtension_2734_; lean_object* v_exportEntriesFn_2735_; lean_object* v_asyncMode_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v_importedEntries_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v_exported_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; uint8_t v___x_2748_; 
v___x_2733_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_2734_ = lean_ctor_get(v___x_2733_, 0);
v_exportEntriesFn_2735_ = lean_ctor_get(v___x_2733_, 4);
v_asyncMode_2736_ = lean_ctor_get(v_toEnvExtension_2734_, 2);
v___x_2737_ = lean_box(1);
v___x_2738_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_2739_ = lean_box(0);
lean_inc_ref_n(v_env_2709_, 2);
v___x_2740_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2738_, v_toEnvExtension_2734_, v_env_2709_, v_asyncMode_2736_, v___x_2739_);
v_importedEntries_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc_ref(v_importedEntries_2741_);
lean_dec(v___x_2740_);
v___x_2742_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2737_, v___x_2733_, v_env_2709_, v_asyncMode_2736_, v___x_2739_);
lean_inc_ref(v_exportEntriesFn_2735_);
v___x_2743_ = lean_apply_2(v_exportEntriesFn_2735_, v_env_2709_, v___x_2742_);
v_exported_2744_ = lean_ctor_get(v___x_2743_, 0);
lean_inc(v_exported_2744_);
lean_dec_ref(v___x_2743_);
v___x_2745_ = lean_array_push(v_importedEntries_2741_, v_exported_2744_);
v___x_2746_ = lean_unsigned_to_nat(0u);
v___x_2747_ = lean_array_get_size(v___x_2745_);
v___x_2748_ = lean_nat_dec_lt(v___x_2746_, v___x_2747_);
if (v___x_2748_ == 0)
{
lean_dec_ref(v___x_2745_);
v___y_2724_ = v___x_2737_;
goto v___jp_2723_;
}
else
{
uint8_t v___x_2749_; 
v___x_2749_ = lean_nat_dec_le(v___x_2747_, v___x_2747_);
if (v___x_2749_ == 0)
{
if (v___x_2748_ == 0)
{
lean_dec_ref(v___x_2745_);
v___y_2724_ = v___x_2737_;
goto v___jp_2723_;
}
else
{
size_t v___x_2750_; size_t v___x_2751_; lean_object* v___x_2752_; 
v___x_2750_ = ((size_t)0ULL);
v___x_2751_ = lean_usize_of_nat(v___x_2747_);
v___x_2752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_2745_, v___x_2750_, v___x_2751_, v___x_2737_);
lean_dec_ref(v___x_2745_);
v___y_2724_ = v___x_2752_;
goto v___jp_2723_;
}
}
else
{
size_t v___x_2753_; size_t v___x_2754_; lean_object* v___x_2755_; 
v___x_2753_ = ((size_t)0ULL);
v___x_2754_ = lean_usize_of_nat(v___x_2747_);
v___x_2755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_2745_, v___x_2753_, v___x_2754_, v___x_2737_);
lean_dec_ref(v___x_2745_);
v___y_2724_ = v___x_2755_;
goto v___jp_2723_;
}
}
v___jp_2723_:
{
lean_object* v_tables_2725_; lean_object* v_leadingTable_2726_; lean_object* v_trailingTable_2727_; lean_object* v_firstTokens_2728_; lean_object* v_firstTokens_2729_; lean_object* v___x_2731_; 
v_tables_2725_ = lean_ctor_get(v_val_2719_, 2);
v_leadingTable_2726_ = lean_ctor_get(v_tables_2725_, 0);
v_trailingTable_2727_ = lean_ctor_get(v_tables_2725_, 2);
lean_inc(v_trailingTable_2727_);
lean_inc(v_leadingTable_2726_);
lean_inc(v_val_2719_);
v_firstTokens_2728_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2719_, v_leadingTable_2726_, v___y_2724_);
v_firstTokens_2729_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2719_, v_trailingTable_2727_, v_firstTokens_2728_);
if (v_isShared_2722_ == 0)
{
lean_ctor_set_tag(v___x_2721_, 0);
lean_ctor_set(v___x_2721_, 0, v_firstTokens_2729_);
v___x_2731_ = v___x_2721_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_firstTokens_2729_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
}
else
{
lean_object* v___x_2757_; lean_object* v___x_2758_; 
lean_dec(v___x_2718_);
lean_dec_ref(v_env_2709_);
v___x_2757_ = lean_box(1);
v___x_2758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2757_);
return v___x_2758_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg___boxed(lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_2759_);
lean_dec(v___y_2759_);
return v_res_2761_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0(void){
_start:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2762_ = lean_box(1);
v___x_2763_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2762_);
return v___x_2763_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2(void){
_start:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2765_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1));
v___x_2766_ = l_Lean_stringToMessageData(v___x_2765_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(lean_object* v_a_2767_, lean_object* v_a_2768_){
_start:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v_env_2773_; lean_object* v_env_2774_; lean_object* v_env_2775_; lean_object* v___x_2776_; lean_object* v_toEnvExtension_2777_; lean_object* v_exportEntriesFn_2778_; lean_object* v_asyncMode_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v_importedEntries_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2836_; 
v___x_2770_ = lean_st_ref_get(v_a_2768_);
v___x_2771_ = lean_st_ref_get(v_a_2768_);
v___x_2772_ = lean_st_ref_get(v_a_2768_);
v_env_2773_ = lean_ctor_get(v___x_2770_, 0);
lean_inc_ref(v_env_2773_);
lean_dec(v___x_2770_);
v_env_2774_ = lean_ctor_get(v___x_2771_, 0);
lean_inc_ref(v_env_2774_);
lean_dec(v___x_2771_);
v_env_2775_ = lean_ctor_get(v___x_2772_, 0);
lean_inc_ref(v_env_2775_);
lean_dec(v___x_2772_);
v___x_2776_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_2777_ = lean_ctor_get(v___x_2776_, 0);
v_exportEntriesFn_2778_ = lean_ctor_get(v___x_2776_, 4);
v_asyncMode_2779_ = lean_ctor_get(v_toEnvExtension_2777_, 2);
v___x_2780_ = lean_box(1);
v___x_2781_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0);
v___x_2782_ = lean_box(0);
v___x_2783_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2781_, v_toEnvExtension_2777_, v_env_2773_, v_asyncMode_2779_, v___x_2782_);
v_importedEntries_2784_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2836_ == 0)
{
lean_object* v_unused_2837_; 
v_unused_2837_ = lean_ctor_get(v___x_2783_, 1);
lean_dec(v_unused_2837_);
v___x_2786_ = v___x_2783_;
v_isShared_2787_ = v_isSharedCheck_2836_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_importedEntries_2784_);
lean_dec(v___x_2783_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2836_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v_exported_2790_; lean_object* v___x_2791_; size_t v_sz_2792_; size_t v___x_2793_; lean_object* v___x_2794_; 
v___x_2788_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2780_, v___x_2776_, v_env_2775_, v_asyncMode_2779_, v___x_2782_);
lean_inc_ref(v_exportEntriesFn_2778_);
v___x_2789_ = lean_apply_2(v_exportEntriesFn_2778_, v_env_2774_, v___x_2788_);
v_exported_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_exported_2790_);
lean_dec_ref(v___x_2789_);
v___x_2791_ = lean_array_push(v_importedEntries_2784_, v_exported_2790_);
v_sz_2792_ = lean_array_size(v___x_2791_);
v___x_2793_ = ((size_t)0ULL);
v___x_2794_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v___x_2791_, v_sz_2792_, v___x_2793_, v___x_2780_, v_a_2767_, v_a_2768_);
lean_dec_ref(v___x_2791_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; lean_object* v___x_2796_; lean_object* v_a_2797_; lean_object* v___x_2798_; 
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_a_2795_);
lean_dec_ref_known(v___x_2794_, 1);
v___x_2796_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v_a_2768_);
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_a_2797_);
lean_dec_ref(v___x_2796_);
v___x_2798_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v_a_2767_, v_a_2768_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v_a_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v_a_2799_ = lean_ctor_get(v___x_2798_, 0);
lean_inc(v_a_2799_);
lean_dec_ref_known(v___x_2798_, 1);
v___x_2800_ = lean_box(0);
v___x_2801_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_2797_, v_a_2795_, v_a_2799_, v___x_2800_, v_a_2767_, v_a_2768_);
lean_dec(v_a_2795_);
lean_dec(v_a_2797_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2807_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2802_);
lean_dec_ref_known(v___x_2801_, 1);
v___x_2803_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2);
v___x_2804_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2805_ = l_Lean_MessageData_joinSep(v_a_2802_, v___x_2804_);
if (v_isShared_2787_ == 0)
{
lean_ctor_set_tag(v___x_2786_, 7);
lean_ctor_set(v___x_2786_, 1, v___x_2805_);
lean_ctor_set(v___x_2786_, 0, v___x_2804_);
v___x_2807_ = v___x_2786_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v___x_2804_);
lean_ctor_set(v_reuseFailAlloc_2811_, 1, v___x_2805_);
v___x_2807_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2808_ = l_Lean_MessageData_nestD(v___x_2807_);
v___x_2809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2803_);
lean_ctor_set(v___x_2809_, 1, v___x_2808_);
v___x_2810_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v___x_2809_, v_a_2767_, v_a_2768_);
return v___x_2810_;
}
}
else
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
lean_del_object(v___x_2786_);
v_a_2812_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2801_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2801_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2817_; 
if (v_isShared_2815_ == 0)
{
v___x_2817_ = v___x_2814_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2812_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
else
{
lean_object* v_a_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
lean_dec(v_a_2797_);
lean_dec(v_a_2795_);
lean_del_object(v___x_2786_);
v_a_2820_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2827_ == 0)
{
v___x_2822_ = v___x_2798_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_a_2820_);
lean_dec(v___x_2798_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2820_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
lean_del_object(v___x_2786_);
v_a_2828_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2794_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2794_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___boxed(lean_object* v_a_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_2838_, v_a_2839_);
lean_dec(v_a_2839_);
lean_dec_ref(v_a_2838_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags(lean_object* v___stx_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_){
_start:
{
lean_object* v___x_2846_; 
v___x_2846_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_2843_, v_a_2844_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed(lean_object* v___stx_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_){
_start:
{
lean_object* v_res_2851_; 
v_res_2851_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags(v___stx_2847_, v_a_2848_, v_a_2849_);
lean_dec(v_a_2849_);
lean_dec_ref(v_a_2848_);
lean_dec(v___stx_2847_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(lean_object* v_00_u03b4_2852_, lean_object* v_t_2853_, lean_object* v_k_2854_, lean_object* v_fallback_2855_){
_start:
{
lean_object* v___x_2856_; 
v___x_2856_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_2853_, v_k_2854_, v_fallback_2855_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___boxed(lean_object* v_00_u03b4_2857_, lean_object* v_t_2858_, lean_object* v_k_2859_, lean_object* v_fallback_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(v_00_u03b4_2857_, v_t_2858_, v_k_2859_, v_fallback_2860_);
lean_dec(v_fallback_2860_);
lean_dec(v_k_2859_);
lean_dec(v_t_2858_);
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(lean_object* v_as_2862_, size_t v_sz_2863_, size_t v_i_2864_, lean_object* v_b_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_){
_start:
{
lean_object* v___x_2869_; 
v___x_2869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_2862_, v_sz_2863_, v_i_2864_, v_b_2865_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___boxed(lean_object* v_as_2870_, lean_object* v_sz_2871_, lean_object* v_i_2872_, lean_object* v_b_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
size_t v_sz_boxed_2877_; size_t v_i_boxed_2878_; lean_object* v_res_2879_; 
v_sz_boxed_2877_ = lean_unbox_usize(v_sz_2871_);
lean_dec(v_sz_2871_);
v_i_boxed_2878_ = lean_unbox_usize(v_i_2872_);
lean_dec(v_i_2872_);
v_res_2879_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(v_as_2870_, v_sz_boxed_2877_, v_i_boxed_2878_, v_b_2873_, v___y_2874_, v___y_2875_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec_ref(v_as_2870_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v___x_2883_; 
v___x_2883_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_2881_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___boxed(lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_){
_start:
{
lean_object* v_res_2887_; 
v_res_2887_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(v___y_2884_, v___y_2885_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(lean_object* v_val_2888_, lean_object* v___x_2889_, lean_object* v___x_2890_, lean_object* v_inst_2891_, lean_object* v_R_2892_, lean_object* v_a_2893_, lean_object* v_b_2894_){
_start:
{
lean_object* v___x_2895_; 
v___x_2895_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2888_, v___x_2889_, v___x_2890_, v_a_2893_, v_b_2894_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___boxed(lean_object* v_val_2896_, lean_object* v___x_2897_, lean_object* v___x_2898_, lean_object* v_inst_2899_, lean_object* v_R_2900_, lean_object* v_a_2901_, lean_object* v_b_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(v_val_2896_, v___x_2897_, v___x_2898_, v_inst_2899_, v_R_2900_, v_a_2901_, v_b_2902_);
lean_dec_ref(v___x_2897_);
lean_dec_ref(v_val_2896_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8(lean_object* v_init_2904_, lean_object* v_t_2905_){
_start:
{
lean_object* v___x_2906_; 
v___x_2906_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__15(v_init_2904_, v_t_2905_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(lean_object* v_n_2907_, lean_object* v_as_2908_, lean_object* v_lo_2909_, lean_object* v_hi_2910_, lean_object* v_w_2911_, lean_object* v_hlo_2912_, lean_object* v_hhi_2913_){
_start:
{
lean_object* v___x_2914_; 
v___x_2914_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_2907_, v_as_2908_, v_lo_2909_, v_hi_2910_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___boxed(lean_object* v_n_2915_, lean_object* v_as_2916_, lean_object* v_lo_2917_, lean_object* v_hi_2918_, lean_object* v_w_2919_, lean_object* v_hlo_2920_, lean_object* v_hhi_2921_){
_start:
{
lean_object* v_res_2922_; 
v_res_2922_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(v_n_2915_, v_as_2916_, v_lo_2917_, v_hi_2918_, v_w_2919_, v_hlo_2920_, v_hhi_2921_);
lean_dec(v_hi_2918_);
lean_dec(v_n_2915_);
return v_res_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(lean_object* v_00_u03b2_2923_, lean_object* v_x_2924_, lean_object* v_x_2925_){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_2924_, v_x_2925_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2927_, lean_object* v_x_2928_, lean_object* v_x_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(v_00_u03b2_2927_, v_x_2928_, v_x_2929_);
lean_dec(v_x_2929_);
lean_dec_ref(v_x_2928_);
return v_res_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(lean_object* v_tac_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
lean_object* v___x_2935_; 
v___x_2935_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_2931_, v___y_2933_);
return v___x_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___boxed(lean_object* v_tac_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
lean_object* v_res_2940_; 
v_res_2940_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(v_tac_2936_, v___y_2937_, v___y_2938_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(lean_object* v_00_u03b4_2941_, lean_object* v_t_2942_, lean_object* v_k_2943_){
_start:
{
lean_object* v___x_2944_; 
v___x_2944_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_t_2942_, v_k_2943_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___boxed(lean_object* v_00_u03b4_2945_, lean_object* v_t_2946_, lean_object* v_k_2947_){
_start:
{
lean_object* v_res_2948_; 
v_res_2948_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(v_00_u03b4_2945_, v_t_2946_, v_k_2947_);
lean_dec(v_k_2947_);
lean_dec(v_t_2946_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(lean_object* v_00_u03b2_2949_, lean_object* v_x_2950_, lean_object* v_x_2951_){
_start:
{
lean_object* v___x_2952_; 
v___x_2952_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_x_2950_, v_x_2951_);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___boxed(lean_object* v_00_u03b2_2953_, lean_object* v_x_2954_, lean_object* v_x_2955_){
_start:
{
lean_object* v_res_2956_; 
v_res_2956_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(v_00_u03b2_2953_, v_x_2954_, v_x_2955_);
lean_dec(v_x_2955_);
lean_dec_ref(v_x_2954_);
return v_res_2956_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(lean_object* v_n_2957_, lean_object* v_lo_2958_, lean_object* v_hi_2959_, lean_object* v_hhi_2960_, lean_object* v_pivot_2961_, lean_object* v_as_2962_, lean_object* v_i_2963_, lean_object* v_k_2964_, lean_object* v_ilo_2965_, lean_object* v_ik_2966_, lean_object* v_w_2967_){
_start:
{
lean_object* v___x_2968_; 
v___x_2968_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___redArg(v_hi_2959_, v_pivot_2961_, v_as_2962_, v_i_2963_, v_k_2964_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17___boxed(lean_object* v_n_2969_, lean_object* v_lo_2970_, lean_object* v_hi_2971_, lean_object* v_hhi_2972_, lean_object* v_pivot_2973_, lean_object* v_as_2974_, lean_object* v_i_2975_, lean_object* v_k_2976_, lean_object* v_ilo_2977_, lean_object* v_ik_2978_, lean_object* v_w_2979_){
_start:
{
lean_object* v_res_2980_; 
v_res_2980_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__17(v_n_2969_, v_lo_2970_, v_hi_2971_, v_hhi_2972_, v_pivot_2973_, v_as_2974_, v_i_2975_, v_k_2976_, v_ilo_2977_, v_ik_2978_, v_w_2979_);
lean_dec(v_hi_2971_);
lean_dec(v_lo_2970_);
lean_dec(v_n_2969_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(lean_object* v_as_2981_, size_t v_sz_2982_, size_t v_i_2983_, lean_object* v_b_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
lean_object* v___x_2988_; 
v___x_2988_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___redArg(v_as_2981_, v_sz_2982_, v_i_2983_, v_b_2984_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19___boxed(lean_object* v_as_2989_, lean_object* v_sz_2990_, lean_object* v_i_2991_, lean_object* v_b_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
size_t v_sz_boxed_2996_; size_t v_i_boxed_2997_; lean_object* v_res_2998_; 
v_sz_boxed_2996_ = lean_unbox_usize(v_sz_2990_);
lean_dec(v_sz_2990_);
v_i_boxed_2997_ = lean_unbox_usize(v_i_2991_);
lean_dec(v_i_2991_);
v_res_2998_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__19(v_as_2989_, v_sz_boxed_2996_, v_i_boxed_2997_, v_b_2992_, v___y_2993_, v___y_2994_);
lean_dec(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec_ref(v_as_2989_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(lean_object* v_init_2999_, lean_object* v_t_3000_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21_spec__25(v_init_2999_, v_t_3000_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___boxed(lean_object* v_init_3002_, lean_object* v_t_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(v_init_3002_, v_t_3003_);
lean_dec(v_t_3003_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(lean_object* v_n_3005_, lean_object* v_as_3006_, lean_object* v_lo_3007_, lean_object* v_hi_3008_, lean_object* v_w_3009_, lean_object* v_hlo_3010_, lean_object* v_hhi_3011_){
_start:
{
lean_object* v___x_3012_; 
v___x_3012_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___redArg(v_n_3005_, v_as_3006_, v_lo_3007_, v_hi_3008_);
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___boxed(lean_object* v_n_3013_, lean_object* v_as_3014_, lean_object* v_lo_3015_, lean_object* v_hi_3016_, lean_object* v_w_3017_, lean_object* v_hlo_3018_, lean_object* v_hhi_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(v_n_3013_, v_as_3014_, v_lo_3015_, v_hi_3016_, v_w_3017_, v_hlo_3018_, v_hhi_3019_);
lean_dec(v_hi_3016_);
lean_dec(v_n_3013_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(lean_object* v_init_3021_, lean_object* v_x_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_){
_start:
{
lean_object* v___x_3026_; 
v___x_3026_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_init_3021_, v_x_3022_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___boxed(lean_object* v_init_3027_, lean_object* v_x_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
lean_object* v_res_3032_; 
v_res_3032_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(v_init_3027_, v_x_3028_, v___y_3029_, v___y_3030_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
return v_res_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_3033_, lean_object* v_x_3034_, size_t v_x_3035_, lean_object* v_x_3036_){
_start:
{
lean_object* v___x_3037_; 
v___x_3037_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_3034_, v_x_3035_, v_x_3036_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_3038_, lean_object* v_x_3039_, lean_object* v_x_3040_, lean_object* v_x_3041_){
_start:
{
size_t v_x_19087__boxed_3042_; lean_object* v_res_3043_; 
v_x_19087__boxed_3042_ = lean_unbox_usize(v_x_3040_);
lean_dec(v_x_3040_);
v_res_3043_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(v_00_u03b2_3038_, v_x_3039_, v_x_19087__boxed_3042_, v_x_3041_);
lean_dec(v_x_3041_);
lean_dec_ref(v_x_3039_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(lean_object* v_as_3044_, lean_object* v_k_3045_, lean_object* v_x_3046_, lean_object* v_x_3047_, lean_object* v_x_3048_){
_start:
{
lean_object* v___x_3049_; 
v___x_3049_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_3044_, v_k_3045_, v_x_3046_, v_x_3047_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___boxed(lean_object* v_as_3050_, lean_object* v_k_3051_, lean_object* v_x_3052_, lean_object* v_x_3053_, lean_object* v_x_3054_){
_start:
{
lean_object* v_res_3055_; 
v_res_3055_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(v_as_3050_, v_k_3051_, v_x_3052_, v_x_3053_, v_x_3054_);
lean_dec_ref(v_k_3051_);
lean_dec_ref(v_as_3050_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(lean_object* v_00_u03b2_3056_, lean_object* v_m_3057_, lean_object* v_a_3058_){
_start:
{
lean_object* v___x_3059_; 
v___x_3059_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___redArg(v_m_3057_, v_a_3058_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14___boxed(lean_object* v_00_u03b2_3060_, lean_object* v_m_3061_, lean_object* v_a_3062_){
_start:
{
lean_object* v_res_3063_; 
v_res_3063_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14(v_00_u03b2_3060_, v_m_3061_, v_a_3062_);
lean_dec(v_a_3062_);
lean_dec_ref(v_m_3061_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(lean_object* v_n_3064_, lean_object* v_lo_3065_, lean_object* v_hi_3066_, lean_object* v_hhi_3067_, lean_object* v_pivot_3068_, lean_object* v_as_3069_, lean_object* v_i_3070_, lean_object* v_k_3071_, lean_object* v_ilo_3072_, lean_object* v_ik_3073_, lean_object* v_w_3074_){
_start:
{
lean_object* v___x_3075_; 
v___x_3075_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___redArg(v_hi_3066_, v_pivot_3068_, v_as_3069_, v_i_3070_, v_k_3071_);
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27___boxed(lean_object* v_n_3076_, lean_object* v_lo_3077_, lean_object* v_hi_3078_, lean_object* v_hhi_3079_, lean_object* v_pivot_3080_, lean_object* v_as_3081_, lean_object* v_i_3082_, lean_object* v_k_3083_, lean_object* v_ilo_3084_, lean_object* v_ik_3085_, lean_object* v_w_3086_){
_start:
{
lean_object* v_res_3087_; 
v_res_3087_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__27(v_n_3076_, v_lo_3077_, v_hi_3078_, v_hhi_3079_, v_pivot_3080_, v_as_3081_, v_i_3082_, v_k_3083_, v_ilo_3084_, v_ik_3085_, v_w_3086_);
lean_dec(v_hi_3078_);
lean_dec(v_lo_3077_);
lean_dec(v_n_3076_);
return v_res_3087_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(lean_object* v_00_u03b2_3088_, lean_object* v_keys_3089_, lean_object* v_vals_3090_, lean_object* v_heq_3091_, lean_object* v_i_3092_, lean_object* v_k_3093_){
_start:
{
lean_object* v___x_3094_; 
v___x_3094_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_3089_, v_vals_3090_, v_i_3092_, v_k_3093_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___boxed(lean_object* v_00_u03b2_3095_, lean_object* v_keys_3096_, lean_object* v_vals_3097_, lean_object* v_heq_3098_, lean_object* v_i_3099_, lean_object* v_k_3100_){
_start:
{
lean_object* v_res_3101_; 
v_res_3101_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(v_00_u03b2_3095_, v_keys_3096_, v_vals_3097_, v_heq_3098_, v_i_3099_, v_k_3100_);
lean_dec(v_k_3100_);
lean_dec_ref(v_vals_3097_);
lean_dec_ref(v_keys_3096_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(lean_object* v_00_u03b2_3102_, lean_object* v_a_3103_, lean_object* v_x_3104_){
_start:
{
lean_object* v___x_3105_; 
v___x_3105_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___redArg(v_a_3103_, v_x_3104_);
return v___x_3105_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22___boxed(lean_object* v_00_u03b2_3106_, lean_object* v_a_3107_, lean_object* v_x_3108_){
_start:
{
lean_object* v_res_3109_; 
v_res_3109_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11_spec__14_spec__22(v_00_u03b2_3106_, v_a_3107_, v_x_3108_);
lean_dec(v_x_3108_);
lean_dec(v_a_3107_);
return v_res_3109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1(){
_start:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3124_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3125_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1));
v___x_3126_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3127_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed), 4, 0);
v___x_3128_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3124_, v___x_3125_, v___x_3126_, v___x_3127_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___boxed(lean_object* v_a_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3(){
_start:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3133_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3134_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0));
v___x_3135_ = l_Lean_addBuiltinDocString(v___x_3133_, v___x_3134_);
return v___x_3135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___boxed(lean_object* v_a_3136_){
_start:
{
lean_object* v_res_3137_; 
v_res_3137_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5(){
_start:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3164_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3165_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6));
v___x_3166_ = l_Lean_addBuiltinDeclarationRanges(v___x_3164_, v___x_3165_);
return v___x_3166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___boxed(lean_object* v_a_3167_){
_start:
{
lean_object* v_res_3168_; 
v_res_3168_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
return v_res_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(lean_object* v_env_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, uint8_t v_includeUnnamed_3172_, lean_object* v_x_3173_, lean_object* v_____s_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_){
_start:
{
lean_object* v_fst_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3233_; 
v_fst_3180_ = lean_ctor_get(v_x_3173_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v_x_3173_);
if (v_isSharedCheck_3233_ == 0)
{
lean_object* v_unused_3234_; 
v_unused_3234_ = lean_ctor_get(v_x_3173_, 1);
lean_dec(v_unused_3234_);
v___x_3182_ = v_x_3173_;
v_isShared_3183_ = v_isSharedCheck_3233_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_fst_3180_);
lean_dec(v_x_3173_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3233_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v_userName_3185_; lean_object* v___y_3186_; lean_object* v___x_3218_; 
lean_inc(v_fst_3180_);
lean_inc_ref(v_env_3169_);
v___x_3218_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_3169_, v_fst_3180_);
if (lean_obj_tag(v___x_3218_) == 1)
{
lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3226_; 
lean_del_object(v___x_3182_);
lean_dec(v_fst_3180_);
lean_dec_ref(v_env_3169_);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3226_ == 0)
{
lean_object* v_unused_3227_; 
v_unused_3227_ = lean_ctor_get(v___x_3218_, 0);
lean_dec(v_unused_3227_);
v___x_3220_ = v___x_3218_;
v_isShared_3221_ = v_isSharedCheck_3226_;
goto v_resetjp_3219_;
}
else
{
lean_dec(v___x_3218_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3226_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3223_; 
if (v_isShared_3221_ == 0)
{
lean_ctor_set(v___x_3220_, 0, v_____s_3174_);
v___x_3223_ = v___x_3220_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_____s_3174_);
v___x_3223_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
lean_object* v___x_3224_; 
v___x_3224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3223_);
return v___x_3224_;
}
}
}
else
{
lean_object* v___x_3228_; 
lean_dec(v___x_3218_);
v___x_3228_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_a_3171_, v_fst_3180_);
if (lean_obj_tag(v___x_3228_) == 1)
{
lean_object* v_val_3229_; 
v_val_3229_ = lean_ctor_get(v___x_3228_, 0);
lean_inc(v_val_3229_);
lean_dec_ref_known(v___x_3228_, 1);
v_userName_3185_ = v_val_3229_;
v___y_3186_ = v___y_3177_;
goto v___jp_3184_;
}
else
{
lean_dec(v___x_3228_);
if (v_includeUnnamed_3172_ == 0)
{
lean_object* v___x_3230_; lean_object* v___x_3231_; 
lean_del_object(v___x_3182_);
lean_dec(v_fst_3180_);
lean_dec_ref(v_env_3169_);
v___x_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3230_, 0, v_____s_3174_);
v___x_3231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3230_);
return v___x_3231_;
}
else
{
lean_object* v___x_3232_; 
lean_inc(v_fst_3180_);
v___x_3232_ = l_Lean_Name_toString(v_fst_3180_, v_includeUnnamed_3172_);
v_userName_3185_ = v___x_3232_;
v___y_3186_ = v___y_3177_;
goto v___jp_3184_;
}
}
}
v___jp_3184_:
{
uint8_t v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = 1;
lean_inc(v_fst_3180_);
lean_inc_ref(v_env_3169_);
v___x_3188_ = l_Lean_findDocString_x3f(v_env_3169_, v_fst_3180_, v___x_3187_);
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3202_; 
lean_del_object(v___x_3182_);
v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3191_ = v___x_3188_;
v_isShared_3192_ = v_isSharedCheck_3202_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3188_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3202_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3200_; 
v___x_3193_ = l_Lean_NameSet_empty;
v___x_3194_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_a_3170_, v_fst_3180_, v___x_3193_);
lean_inc(v_fst_3180_);
v___x_3195_ = l_Lean_Parser_Tactic_Doc_getTacticExtensions(v_env_3169_, v_fst_3180_);
v___x_3196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3196_, 0, v_fst_3180_);
lean_ctor_set(v___x_3196_, 1, v_userName_3185_);
lean_ctor_set(v___x_3196_, 2, v___x_3194_);
lean_ctor_set(v___x_3196_, 3, v_a_3189_);
lean_ctor_set(v___x_3196_, 4, v___x_3195_);
v___x_3197_ = lean_array_push(v_____s_3174_, v___x_3196_);
v___x_3198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3197_);
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 0, v___x_3198_);
v___x_3200_ = v___x_3191_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v___x_3198_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
else
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3217_; 
lean_dec_ref(v_userName_3185_);
lean_dec(v_fst_3180_);
lean_dec_ref(v_____s_3174_);
lean_dec_ref(v_env_3169_);
v_a_3203_ = lean_ctor_get(v___x_3188_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3205_ = v___x_3188_;
v_isShared_3206_ = v_isSharedCheck_3217_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3188_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3217_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v_ref_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3212_; 
v_ref_3207_ = lean_ctor_get(v___y_3186_, 5);
v___x_3208_ = lean_io_error_to_string(v_a_3203_);
v___x_3209_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3208_);
v___x_3210_ = l_Lean_MessageData_ofFormat(v___x_3209_);
lean_inc(v_ref_3207_);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 1, v___x_3210_);
lean_ctor_set(v___x_3182_, 0, v_ref_3207_);
v___x_3212_ = v___x_3182_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_ref_3207_);
lean_ctor_set(v_reuseFailAlloc_3216_, 1, v___x_3210_);
v___x_3212_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
lean_object* v___x_3214_; 
if (v_isShared_3206_ == 0)
{
lean_ctor_set(v___x_3205_, 0, v___x_3212_);
v___x_3214_ = v___x_3205_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___x_3212_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed(lean_object* v_env_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_includeUnnamed_3238_, lean_object* v_x_3239_, lean_object* v_____s_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
uint8_t v_includeUnnamed_boxed_3246_; lean_object* v_res_3247_; 
v_includeUnnamed_boxed_3246_ = lean_unbox(v_includeUnnamed_3238_);
v_res_3247_ = l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(v_env_3235_, v_a_3236_, v_a_3237_, v_includeUnnamed_boxed_3246_, v_x_3239_, v_____s_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
lean_dec(v_a_3237_);
lean_dec(v_a_3236_);
return v_res_3247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(lean_object* v_as_3248_, size_t v_sz_3249_, size_t v_i_3250_, lean_object* v_b_3251_){
_start:
{
uint8_t v___x_3253_; 
v___x_3253_ = lean_usize_dec_lt(v_i_3250_, v_sz_3249_);
if (v___x_3253_ == 0)
{
lean_object* v___x_3254_; 
v___x_3254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3254_, 0, v_b_3251_);
return v___x_3254_;
}
else
{
lean_object* v_a_3255_; lean_object* v_fst_3256_; lean_object* v_snd_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; size_t v___x_3262_; size_t v___x_3263_; 
v_a_3255_ = lean_array_uget_borrowed(v_as_3248_, v_i_3250_);
v_fst_3256_ = lean_ctor_get(v_a_3255_, 0);
v_snd_3257_ = lean_ctor_get(v_a_3255_, 1);
v___x_3258_ = l_Lean_NameSet_empty;
v___x_3259_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_3251_, v_fst_3256_, v___x_3258_);
lean_inc(v_snd_3257_);
v___x_3260_ = l_Lean_NameSet_insert(v___x_3259_, v_snd_3257_);
lean_inc(v_fst_3256_);
v___x_3261_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3256_, v___x_3260_, v_b_3251_);
v___x_3262_ = ((size_t)1ULL);
v___x_3263_ = lean_usize_add(v_i_3250_, v___x_3262_);
v_i_3250_ = v___x_3263_;
v_b_3251_ = v___x_3261_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg___boxed(lean_object* v_as_3265_, lean_object* v_sz_3266_, lean_object* v_i_3267_, lean_object* v_b_3268_, lean_object* v___y_3269_){
_start:
{
size_t v_sz_boxed_3270_; size_t v_i_boxed_3271_; lean_object* v_res_3272_; 
v_sz_boxed_3270_ = lean_unbox_usize(v_sz_3266_);
lean_dec(v_sz_3266_);
v_i_boxed_3271_ = lean_unbox_usize(v_i_3267_);
lean_dec(v_i_3267_);
v_res_3272_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_3265_, v_sz_boxed_3270_, v_i_boxed_3271_, v_b_3268_);
lean_dec_ref(v_as_3265_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(lean_object* v_as_3273_, size_t v_sz_3274_, size_t v_i_3275_, lean_object* v_b_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
uint8_t v___x_3282_; 
v___x_3282_ = lean_usize_dec_lt(v_i_3275_, v_sz_3274_);
if (v___x_3282_ == 0)
{
lean_object* v___x_3283_; 
v___x_3283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3283_, 0, v_b_3276_);
return v___x_3283_;
}
else
{
lean_object* v_a_3284_; size_t v_sz_3285_; size_t v___x_3286_; lean_object* v___x_3287_; 
v_a_3284_ = lean_array_uget_borrowed(v_as_3273_, v_i_3275_);
v_sz_3285_ = lean_array_size(v_a_3284_);
v___x_3286_ = ((size_t)0ULL);
v___x_3287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_a_3284_, v_sz_3285_, v___x_3286_, v_b_3276_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_object* v_a_3288_; size_t v___x_3289_; size_t v___x_3290_; 
v_a_3288_ = lean_ctor_get(v___x_3287_, 0);
lean_inc(v_a_3288_);
lean_dec_ref_known(v___x_3287_, 1);
v___x_3289_ = ((size_t)1ULL);
v___x_3290_ = lean_usize_add(v_i_3275_, v___x_3289_);
v_i_3275_ = v___x_3290_;
v_b_3276_ = v_a_3288_;
goto _start;
}
else
{
return v___x_3287_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1___boxed(lean_object* v_as_3292_, lean_object* v_sz_3293_, lean_object* v_i_3294_, lean_object* v_b_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_){
_start:
{
size_t v_sz_boxed_3301_; size_t v_i_boxed_3302_; lean_object* v_res_3303_; 
v_sz_boxed_3301_ = lean_unbox_usize(v_sz_3293_);
lean_dec(v_sz_3293_);
v_i_boxed_3302_ = lean_unbox_usize(v_i_3294_);
lean_dec(v_i_3294_);
v_res_3303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v_as_3292_, v_sz_boxed_3301_, v_i_boxed_3302_, v_b_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
lean_dec_ref(v_as_3292_);
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(lean_object* v_f_3304_, lean_object* v_keys_3305_, lean_object* v_vals_3306_, lean_object* v_i_3307_, lean_object* v_acc_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
lean_object* v___x_3314_; uint8_t v___x_3315_; 
v___x_3314_ = lean_array_get_size(v_keys_3305_);
v___x_3315_ = lean_nat_dec_lt(v_i_3307_, v___x_3314_);
if (v___x_3315_ == 0)
{
lean_object* v___x_3316_; lean_object* v___x_3317_; 
lean_dec(v_i_3307_);
lean_dec_ref(v_f_3304_);
v___x_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3316_, 0, v_acc_3308_);
v___x_3317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3316_);
return v___x_3317_;
}
else
{
lean_object* v_k_3318_; lean_object* v_v_3319_; lean_object* v___x_3320_; 
v_k_3318_ = lean_array_fget_borrowed(v_keys_3305_, v_i_3307_);
v_v_3319_ = lean_array_fget_borrowed(v_vals_3306_, v_i_3307_);
lean_inc_ref(v_f_3304_);
lean_inc(v___y_3312_);
lean_inc_ref(v___y_3311_);
lean_inc(v___y_3310_);
lean_inc_ref(v___y_3309_);
lean_inc(v_v_3319_);
lean_inc(v_k_3318_);
v___x_3320_ = lean_apply_8(v_f_3304_, v_acc_3308_, v_k_3318_, v_v_3319_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, lean_box(0));
if (lean_obj_tag(v___x_3320_) == 0)
{
lean_object* v_a_3321_; 
v_a_3321_ = lean_ctor_get(v___x_3320_, 0);
lean_inc(v_a_3321_);
if (lean_obj_tag(v_a_3321_) == 0)
{
lean_dec_ref_known(v_a_3321_, 1);
lean_dec(v_i_3307_);
lean_dec_ref(v_f_3304_);
return v___x_3320_;
}
else
{
lean_object* v_a_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
lean_dec_ref_known(v___x_3320_, 1);
v_a_3322_ = lean_ctor_get(v_a_3321_, 0);
lean_inc(v_a_3322_);
lean_dec_ref_known(v_a_3321_, 1);
v___x_3323_ = lean_unsigned_to_nat(1u);
v___x_3324_ = lean_nat_add(v_i_3307_, v___x_3323_);
lean_dec(v_i_3307_);
v_i_3307_ = v___x_3324_;
v_acc_3308_ = v_a_3322_;
goto _start;
}
}
else
{
lean_dec(v_i_3307_);
lean_dec_ref(v_f_3304_);
return v___x_3320_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_f_3326_, lean_object* v_keys_3327_, lean_object* v_vals_3328_, lean_object* v_i_3329_, lean_object* v_acc_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3326_, v_keys_3327_, v_vals_3328_, v_i_3329_, v_acc_3330_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3331_);
lean_dec_ref(v_vals_3328_);
lean_dec_ref(v_keys_3327_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(lean_object* v_f_3337_, lean_object* v_x_3338_, lean_object* v_x_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_){
_start:
{
if (lean_obj_tag(v_x_3338_) == 0)
{
lean_object* v_es_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3367_; 
v_es_3345_ = lean_ctor_get(v_x_3338_, 0);
v_isSharedCheck_3367_ = !lean_is_exclusive(v_x_3338_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3347_ = v_x_3338_;
v_isShared_3348_ = v_isSharedCheck_3367_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_es_3345_);
lean_dec(v_x_3338_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3367_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; uint8_t v___x_3351_; 
v___x_3349_ = lean_unsigned_to_nat(0u);
v___x_3350_ = lean_array_get_size(v_es_3345_);
v___x_3351_ = lean_nat_dec_lt(v___x_3349_, v___x_3350_);
if (v___x_3351_ == 0)
{
lean_object* v___x_3353_; 
lean_dec_ref(v_es_3345_);
lean_dec_ref(v_f_3337_);
if (v_isShared_3348_ == 0)
{
lean_ctor_set_tag(v___x_3347_, 1);
lean_ctor_set(v___x_3347_, 0, v_x_3339_);
v___x_3353_ = v___x_3347_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_x_3339_);
v___x_3353_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
lean_object* v___x_3354_; 
v___x_3354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3353_);
return v___x_3354_;
}
}
else
{
uint8_t v___x_3356_; 
v___x_3356_ = lean_nat_dec_le(v___x_3350_, v___x_3350_);
if (v___x_3356_ == 0)
{
if (v___x_3351_ == 0)
{
lean_object* v___x_3358_; 
lean_dec_ref(v_es_3345_);
lean_dec_ref(v_f_3337_);
if (v_isShared_3348_ == 0)
{
lean_ctor_set_tag(v___x_3347_, 1);
lean_ctor_set(v___x_3347_, 0, v_x_3339_);
v___x_3358_ = v___x_3347_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_x_3339_);
v___x_3358_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
lean_object* v___x_3359_; 
v___x_3359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3358_);
return v___x_3359_;
}
}
else
{
size_t v___x_3361_; size_t v___x_3362_; lean_object* v___x_3363_; 
lean_del_object(v___x_3347_);
v___x_3361_ = ((size_t)0ULL);
v___x_3362_ = lean_usize_of_nat(v___x_3350_);
v___x_3363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3337_, v_es_3345_, v___x_3361_, v___x_3362_, v_x_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_);
lean_dec_ref(v_es_3345_);
return v___x_3363_;
}
}
else
{
size_t v___x_3364_; size_t v___x_3365_; lean_object* v___x_3366_; 
lean_del_object(v___x_3347_);
v___x_3364_ = ((size_t)0ULL);
v___x_3365_ = lean_usize_of_nat(v___x_3350_);
v___x_3366_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3337_, v_es_3345_, v___x_3364_, v___x_3365_, v_x_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_);
lean_dec_ref(v_es_3345_);
return v___x_3366_;
}
}
}
}
else
{
lean_object* v_ks_3368_; lean_object* v_vs_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; 
v_ks_3368_ = lean_ctor_get(v_x_3338_, 0);
lean_inc_ref(v_ks_3368_);
v_vs_3369_ = lean_ctor_get(v_x_3338_, 1);
lean_inc_ref(v_vs_3369_);
lean_dec_ref_known(v_x_3338_, 2);
v___x_3370_ = lean_unsigned_to_nat(0u);
v___x_3371_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3337_, v_ks_3368_, v_vs_3369_, v___x_3370_, v_x_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_);
lean_dec_ref(v_vs_3369_);
lean_dec_ref(v_ks_3368_);
return v___x_3371_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(lean_object* v_f_3372_, lean_object* v_as_3373_, size_t v_i_3374_, size_t v_stop_3375_, lean_object* v_b_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
lean_object* v_a_3383_; lean_object* v___y_3388_; uint8_t v___x_3391_; 
v___x_3391_ = lean_usize_dec_eq(v_i_3374_, v_stop_3375_);
if (v___x_3391_ == 0)
{
lean_object* v___x_3392_; 
v___x_3392_ = lean_array_uget_borrowed(v_as_3373_, v_i_3374_);
switch(lean_obj_tag(v___x_3392_))
{
case 0:
{
lean_object* v_key_3393_; lean_object* v_val_3394_; lean_object* v___x_3395_; 
v_key_3393_ = lean_ctor_get(v___x_3392_, 0);
v_val_3394_ = lean_ctor_get(v___x_3392_, 1);
lean_inc_ref(v_f_3372_);
lean_inc(v___y_3380_);
lean_inc_ref(v___y_3379_);
lean_inc(v___y_3378_);
lean_inc_ref(v___y_3377_);
lean_inc(v_val_3394_);
lean_inc(v_key_3393_);
v___x_3395_ = lean_apply_8(v_f_3372_, v_b_3376_, v_key_3393_, v_val_3394_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_, lean_box(0));
v___y_3388_ = v___x_3395_;
goto v___jp_3387_;
}
case 1:
{
lean_object* v_node_3396_; lean_object* v___x_3397_; 
v_node_3396_ = lean_ctor_get(v___x_3392_, 0);
lean_inc(v_node_3396_);
lean_inc_ref(v_f_3372_);
v___x_3397_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3372_, v_node_3396_, v_b_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
v___y_3388_ = v___x_3397_;
goto v___jp_3387_;
}
default: 
{
v_a_3383_ = v_b_3376_;
goto v___jp_3382_;
}
}
}
else
{
lean_object* v___x_3398_; lean_object* v___x_3399_; 
lean_dec_ref(v_f_3372_);
v___x_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3398_, 0, v_b_3376_);
v___x_3399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3398_);
return v___x_3399_;
}
v___jp_3382_:
{
size_t v___x_3384_; size_t v___x_3385_; 
v___x_3384_ = ((size_t)1ULL);
v___x_3385_ = lean_usize_add(v_i_3374_, v___x_3384_);
v_i_3374_ = v___x_3385_;
v_b_3376_ = v_a_3383_;
goto _start;
}
v___jp_3387_:
{
if (lean_obj_tag(v___y_3388_) == 0)
{
lean_object* v_a_3389_; 
v_a_3389_ = lean_ctor_get(v___y_3388_, 0);
if (lean_obj_tag(v_a_3389_) == 0)
{
lean_dec_ref(v_f_3372_);
return v___y_3388_;
}
else
{
lean_object* v_a_3390_; 
lean_inc_ref(v_a_3389_);
lean_dec_ref_known(v___y_3388_, 1);
v_a_3390_ = lean_ctor_get(v_a_3389_, 0);
lean_inc(v_a_3390_);
lean_dec_ref_known(v_a_3389_, 1);
v_a_3383_ = v_a_3390_;
goto v___jp_3382_;
}
}
else
{
lean_dec_ref(v_f_3372_);
return v___y_3388_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_f_3400_, lean_object* v_as_3401_, lean_object* v_i_3402_, lean_object* v_stop_3403_, lean_object* v_b_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_){
_start:
{
size_t v_i_boxed_3410_; size_t v_stop_boxed_3411_; lean_object* v_res_3412_; 
v_i_boxed_3410_ = lean_unbox_usize(v_i_3402_);
lean_dec(v_i_3402_);
v_stop_boxed_3411_ = lean_unbox_usize(v_stop_3403_);
lean_dec(v_stop_3403_);
v_res_3412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3400_, v_as_3401_, v_i_boxed_3410_, v_stop_boxed_3411_, v_b_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_);
lean_dec(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec_ref(v_as_3401_);
return v_res_3412_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_f_3413_, lean_object* v_x_3414_, lean_object* v_x_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
lean_object* v_res_3421_; 
v_res_3421_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3413_, v_x_3414_, v_x_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
return v_res_3421_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(lean_object* v_f_3422_, lean_object* v_s_3423_, lean_object* v_a_3424_, lean_object* v_b_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_){
_start:
{
lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3431_, 0, v_a_3424_);
lean_ctor_set(v___x_3431_, 1, v_b_3425_);
lean_inc(v___y_3429_);
lean_inc_ref(v___y_3428_);
lean_inc(v___y_3427_);
lean_inc_ref(v___y_3426_);
v___x_3432_ = lean_apply_7(v_f_3422_, v___x_3431_, v_s_3423_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, lean_box(0));
if (lean_obj_tag(v___x_3432_) == 0)
{
lean_object* v_a_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3459_; 
v_a_3433_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3435_ = v___x_3432_;
v_isShared_3436_ = v_isSharedCheck_3459_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_a_3433_);
lean_dec(v___x_3432_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3459_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
if (lean_obj_tag(v_a_3433_) == 0)
{
lean_object* v_a_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3447_; 
v_a_3437_ = lean_ctor_get(v_a_3433_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v_a_3433_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3439_ = v_a_3433_;
v_isShared_3440_ = v_isSharedCheck_3447_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_a_3437_);
lean_dec(v_a_3433_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3447_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3442_; 
if (v_isShared_3440_ == 0)
{
v___x_3442_ = v___x_3439_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_a_3437_);
v___x_3442_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
lean_object* v___x_3444_; 
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 0, v___x_3442_);
v___x_3444_ = v___x_3435_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___x_3442_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
}
}
else
{
lean_object* v_a_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3458_; 
v_a_3448_ = lean_ctor_get(v_a_3433_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v_a_3433_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3450_ = v_a_3433_;
v_isShared_3451_ = v_isSharedCheck_3458_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_a_3448_);
lean_dec(v_a_3433_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3458_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3453_; 
if (v_isShared_3451_ == 0)
{
v___x_3453_ = v___x_3450_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_a_3448_);
v___x_3453_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
lean_object* v___x_3455_; 
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 0, v___x_3453_);
v___x_3455_ = v___x_3435_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v___x_3453_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
}
}
}
}
else
{
lean_object* v_a_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3467_; 
v_a_3460_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3462_ = v___x_3432_;
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_a_3460_);
lean_dec(v___x_3432_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed(lean_object* v_f_3468_, lean_object* v_s_3469_, lean_object* v_a_3470_, lean_object* v_b_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_){
_start:
{
lean_object* v_res_3477_; 
v_res_3477_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(v_f_3468_, v_s_3469_, v_a_3470_, v_b_3471_, v___y_3472_, v___y_3473_, v___y_3474_, v___y_3475_);
lean_dec(v___y_3475_);
lean_dec_ref(v___y_3474_);
lean_dec(v___y_3473_);
lean_dec_ref(v___y_3472_);
return v_res_3477_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(lean_object* v_map_3478_, lean_object* v_init_3479_, lean_object* v_f_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_){
_start:
{
lean_object* v___f_3486_; lean_object* v___x_3487_; 
v___f_3486_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3486_, 0, v_f_3480_);
lean_inc_ref(v_map_3478_);
v___x_3487_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v___f_3486_, v_map_3478_, v_init_3479_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
if (lean_obj_tag(v___x_3487_) == 0)
{
lean_object* v_a_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3496_; 
v_a_3488_ = lean_ctor_get(v___x_3487_, 0);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3490_ = v___x_3487_;
v_isShared_3491_ = v_isSharedCheck_3496_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_a_3488_);
lean_dec(v___x_3487_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3496_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v_a_3492_; lean_object* v___x_3494_; 
v_a_3492_ = lean_ctor_get(v_a_3488_, 0);
lean_inc(v_a_3492_);
lean_dec(v_a_3488_);
if (v_isShared_3491_ == 0)
{
lean_ctor_set(v___x_3490_, 0, v_a_3492_);
v___x_3494_ = v___x_3490_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_a_3492_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
else
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3504_; 
v_a_3497_ = lean_ctor_get(v___x_3487_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3487_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3499_ = v___x_3487_;
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3487_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3502_; 
if (v_isShared_3500_ == 0)
{
v___x_3502_ = v___x_3499_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3497_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___boxed(lean_object* v_map_3505_, lean_object* v_init_3506_, lean_object* v_f_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_){
_start:
{
lean_object* v_res_3513_; 
v_res_3513_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_3505_, v_init_3506_, v_f_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_);
lean_dec(v___y_3511_);
lean_dec_ref(v___y_3510_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec_ref(v_map_3505_);
return v_res_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(lean_object* v___y_3514_){
_start:
{
lean_object* v___x_3516_; lean_object* v_env_3517_; lean_object* v___x_3518_; lean_object* v_ext_3519_; lean_object* v_toEnvExtension_3520_; lean_object* v_asyncMode_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v_categories_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3516_ = lean_st_ref_get(v___y_3514_);
v_env_3517_ = lean_ctor_get(v___x_3516_, 0);
lean_inc_ref_n(v_env_3517_, 2);
lean_dec(v___x_3516_);
v___x_3518_ = l_Lean_Parser_parserExtension;
v_ext_3519_ = lean_ctor_get(v___x_3518_, 1);
v_toEnvExtension_3520_ = lean_ctor_get(v_ext_3519_, 0);
v_asyncMode_3521_ = lean_ctor_get(v_toEnvExtension_3520_, 2);
v___x_3522_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3523_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3522_, v___x_3518_, v_env_3517_, v_asyncMode_3521_);
v_categories_3524_ = lean_ctor_get(v___x_3523_, 2);
lean_inc_ref(v_categories_3524_);
lean_dec(v___x_3523_);
v___x_3525_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_3526_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_3524_, v___x_3525_);
lean_dec_ref(v_categories_3524_);
if (lean_obj_tag(v___x_3526_) == 1)
{
lean_object* v_val_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3564_; 
v_val_3527_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3529_ = v___x_3526_;
v_isShared_3530_ = v_isSharedCheck_3564_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_val_3527_);
lean_dec(v___x_3526_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3564_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v___y_3532_; lean_object* v___x_3541_; lean_object* v_toEnvExtension_3542_; lean_object* v_exportEntriesFn_3543_; lean_object* v_asyncMode_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v_importedEntries_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v_exported_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; uint8_t v___x_3556_; 
v___x_3541_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3542_ = lean_ctor_get(v___x_3541_, 0);
v_exportEntriesFn_3543_ = lean_ctor_get(v___x_3541_, 4);
v_asyncMode_3544_ = lean_ctor_get(v_toEnvExtension_3542_, 2);
v___x_3545_ = lean_box(1);
v___x_3546_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_3547_ = lean_box(0);
lean_inc_ref_n(v_env_3517_, 2);
v___x_3548_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3546_, v_toEnvExtension_3542_, v_env_3517_, v_asyncMode_3544_, v___x_3547_);
v_importedEntries_3549_ = lean_ctor_get(v___x_3548_, 0);
lean_inc_ref(v_importedEntries_3549_);
lean_dec(v___x_3548_);
v___x_3550_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3545_, v___x_3541_, v_env_3517_, v_asyncMode_3544_, v___x_3547_);
lean_inc_ref(v_exportEntriesFn_3543_);
v___x_3551_ = lean_apply_2(v_exportEntriesFn_3543_, v_env_3517_, v___x_3550_);
v_exported_3552_ = lean_ctor_get(v___x_3551_, 0);
lean_inc(v_exported_3552_);
lean_dec_ref(v___x_3551_);
v___x_3553_ = lean_array_push(v_importedEntries_3549_, v_exported_3552_);
v___x_3554_ = lean_unsigned_to_nat(0u);
v___x_3555_ = lean_array_get_size(v___x_3553_);
v___x_3556_ = lean_nat_dec_lt(v___x_3554_, v___x_3555_);
if (v___x_3556_ == 0)
{
lean_dec_ref(v___x_3553_);
v___y_3532_ = v___x_3545_;
goto v___jp_3531_;
}
else
{
uint8_t v___x_3557_; 
v___x_3557_ = lean_nat_dec_le(v___x_3555_, v___x_3555_);
if (v___x_3557_ == 0)
{
if (v___x_3556_ == 0)
{
lean_dec_ref(v___x_3553_);
v___y_3532_ = v___x_3545_;
goto v___jp_3531_;
}
else
{
size_t v___x_3558_; size_t v___x_3559_; lean_object* v___x_3560_; 
v___x_3558_ = ((size_t)0ULL);
v___x_3559_ = lean_usize_of_nat(v___x_3555_);
v___x_3560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3553_, v___x_3558_, v___x_3559_, v___x_3545_);
lean_dec_ref(v___x_3553_);
v___y_3532_ = v___x_3560_;
goto v___jp_3531_;
}
}
else
{
size_t v___x_3561_; size_t v___x_3562_; lean_object* v___x_3563_; 
v___x_3561_ = ((size_t)0ULL);
v___x_3562_ = lean_usize_of_nat(v___x_3555_);
v___x_3563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3553_, v___x_3561_, v___x_3562_, v___x_3545_);
lean_dec_ref(v___x_3553_);
v___y_3532_ = v___x_3563_;
goto v___jp_3531_;
}
}
v___jp_3531_:
{
lean_object* v_tables_3533_; lean_object* v_leadingTable_3534_; lean_object* v_trailingTable_3535_; lean_object* v_firstTokens_3536_; lean_object* v_firstTokens_3537_; lean_object* v___x_3539_; 
v_tables_3533_ = lean_ctor_get(v_val_3527_, 2);
v_leadingTable_3534_ = lean_ctor_get(v_tables_3533_, 0);
v_trailingTable_3535_ = lean_ctor_get(v_tables_3533_, 2);
lean_inc(v_trailingTable_3535_);
lean_inc(v_leadingTable_3534_);
lean_inc(v_val_3527_);
v_firstTokens_3536_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_3527_, v_leadingTable_3534_, v___y_3532_);
v_firstTokens_3537_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_3527_, v_trailingTable_3535_, v_firstTokens_3536_);
if (v_isShared_3530_ == 0)
{
lean_ctor_set_tag(v___x_3529_, 0);
lean_ctor_set(v___x_3529_, 0, v_firstTokens_3537_);
v___x_3539_ = v___x_3529_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_firstTokens_3537_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
}
else
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
lean_dec(v___x_3526_);
lean_dec_ref(v_env_3517_);
v___x_3565_ = lean_box(1);
v___x_3566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3566_, 0, v___x_3565_);
return v___x_3566_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg___boxed(lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v_res_3569_; 
v_res_3569_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_3567_);
lean_dec(v___y_3567_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs(uint8_t v_includeUnnamed_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_){
_start:
{
lean_object* v___x_3578_; lean_object* v_env_3579_; lean_object* v___x_3580_; lean_object* v_toEnvExtension_3581_; lean_object* v_exportEntriesFn_3582_; lean_object* v_asyncMode_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v_importedEntries_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v_exported_3591_; lean_object* v___x_3592_; size_t v_sz_3593_; size_t v___x_3594_; lean_object* v___x_3595_; 
v___x_3578_ = lean_st_ref_get(v_a_3576_);
v_env_3579_ = lean_ctor_get(v___x_3578_, 0);
lean_inc_ref_n(v_env_3579_, 4);
lean_dec(v___x_3578_);
v___x_3580_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_3581_ = lean_ctor_get(v___x_3580_, 0);
v_exportEntriesFn_3582_ = lean_ctor_get(v___x_3580_, 4);
v_asyncMode_3583_ = lean_ctor_get(v_toEnvExtension_3581_, 2);
v___x_3584_ = lean_box(1);
v___x_3585_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0);
v___x_3586_ = lean_box(0);
v___x_3587_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3585_, v_toEnvExtension_3581_, v_env_3579_, v_asyncMode_3583_, v___x_3586_);
v_importedEntries_3588_ = lean_ctor_get(v___x_3587_, 0);
lean_inc_ref(v_importedEntries_3588_);
lean_dec(v___x_3587_);
v___x_3589_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3584_, v___x_3580_, v_env_3579_, v_asyncMode_3583_, v___x_3586_);
lean_inc_ref(v_exportEntriesFn_3582_);
v___x_3590_ = lean_apply_2(v_exportEntriesFn_3582_, v_env_3579_, v___x_3589_);
v_exported_3591_ = lean_ctor_get(v___x_3590_, 0);
lean_inc(v_exported_3591_);
lean_dec_ref(v___x_3590_);
v___x_3592_ = lean_array_push(v_importedEntries_3588_, v_exported_3591_);
v_sz_3593_ = lean_array_size(v___x_3592_);
v___x_3594_ = ((size_t)0ULL);
v___x_3595_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v___x_3592_, v_sz_3593_, v___x_3594_, v___x_3584_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_);
lean_dec_ref(v___x_3592_);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_object* v_a_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3620_; 
v_a_3596_ = lean_ctor_get(v___x_3595_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3598_ = v___x_3595_;
v_isShared_3599_ = v_isSharedCheck_3620_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_a_3596_);
lean_dec(v___x_3595_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3620_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3600_; lean_object* v_ext_3601_; lean_object* v_toEnvExtension_3602_; lean_object* v_asyncMode_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v_categories_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; 
v___x_3600_ = l_Lean_Parser_parserExtension;
v_ext_3601_ = lean_ctor_get(v___x_3600_, 1);
v_toEnvExtension_3602_ = lean_ctor_get(v_ext_3601_, 0);
v_asyncMode_3603_ = lean_ctor_get(v_toEnvExtension_3602_, 2);
v___x_3604_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_inc_ref(v_env_3579_);
v___x_3605_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3604_, v___x_3600_, v_env_3579_, v_asyncMode_3603_);
v_categories_3606_ = lean_ctor_get(v___x_3605_, 2);
lean_inc_ref(v_categories_3606_);
lean_dec(v___x_3605_);
v___x_3607_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0));
v___x_3608_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_3609_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_3606_, v___x_3608_);
lean_dec_ref(v_categories_3606_);
if (lean_obj_tag(v___x_3609_) == 1)
{
lean_object* v_val_3610_; lean_object* v___x_3611_; lean_object* v_a_3612_; lean_object* v_kinds_3613_; lean_object* v___x_3614_; lean_object* v___f_3615_; lean_object* v___x_3616_; 
lean_del_object(v___x_3598_);
v_val_3610_ = lean_ctor_get(v___x_3609_, 0);
lean_inc(v_val_3610_);
lean_dec_ref_known(v___x_3609_, 1);
v___x_3611_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v_a_3576_);
v_a_3612_ = lean_ctor_get(v___x_3611_, 0);
lean_inc(v_a_3612_);
lean_dec_ref(v___x_3611_);
v_kinds_3613_ = lean_ctor_get(v_val_3610_, 1);
lean_inc_ref(v_kinds_3613_);
lean_dec(v_val_3610_);
v___x_3614_ = lean_box(v_includeUnnamed_3572_);
v___f_3615_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed), 11, 4);
lean_closure_set(v___f_3615_, 0, v_env_3579_);
lean_closure_set(v___f_3615_, 1, v_a_3596_);
lean_closure_set(v___f_3615_, 2, v_a_3612_);
lean_closure_set(v___f_3615_, 3, v___x_3614_);
v___x_3616_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_kinds_3613_, v___x_3607_, v___f_3615_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_);
lean_dec_ref(v_kinds_3613_);
return v___x_3616_;
}
else
{
lean_object* v___x_3618_; 
lean_dec(v___x_3609_);
lean_dec(v_a_3596_);
lean_dec_ref(v_env_3579_);
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 0, v___x_3607_);
v___x_3618_ = v___x_3598_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v___x_3607_);
v___x_3618_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
return v___x_3618_;
}
}
}
}
else
{
lean_object* v_a_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3628_; 
lean_dec_ref(v_env_3579_);
v_a_3621_ = lean_ctor_get(v___x_3595_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3623_ = v___x_3595_;
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_a_3621_);
lean_dec(v___x_3595_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3626_; 
if (v_isShared_3624_ == 0)
{
v___x_3626_ = v___x_3623_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3621_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___boxed(lean_object* v_includeUnnamed_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_){
_start:
{
uint8_t v_includeUnnamed_boxed_3635_; lean_object* v_res_3636_; 
v_includeUnnamed_boxed_3635_ = lean_unbox(v_includeUnnamed_3629_);
v_res_3636_ = l_Lean_Elab_Tactic_Doc_allTacticDocs(v_includeUnnamed_boxed_3635_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_);
lean_dec(v_a_3633_);
lean_dec_ref(v_a_3632_);
lean_dec(v_a_3631_);
lean_dec_ref(v_a_3630_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(lean_object* v_as_3637_, size_t v_sz_3638_, size_t v_i_3639_, lean_object* v_b_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_){
_start:
{
lean_object* v___x_3646_; 
v___x_3646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_3637_, v_sz_3638_, v_i_3639_, v_b_3640_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___boxed(lean_object* v_as_3647_, lean_object* v_sz_3648_, lean_object* v_i_3649_, lean_object* v_b_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_){
_start:
{
size_t v_sz_boxed_3656_; size_t v_i_boxed_3657_; lean_object* v_res_3658_; 
v_sz_boxed_3656_ = lean_unbox_usize(v_sz_3648_);
lean_dec(v_sz_3648_);
v_i_boxed_3657_ = lean_unbox_usize(v_i_3649_);
lean_dec(v_i_3649_);
v_res_3658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(v_as_3647_, v_sz_boxed_3656_, v_i_boxed_3657_, v_b_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec_ref(v_as_3647_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_){
_start:
{
lean_object* v___x_3664_; 
v___x_3664_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_3662_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___boxed(lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_){
_start:
{
lean_object* v_res_3670_; 
v_res_3670_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec(v___y_3666_);
lean_dec_ref(v___y_3665_);
return v_res_3670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(lean_object* v_00_u03c3_3671_, lean_object* v_00_u03b2_3672_, lean_object* v_map_3673_, lean_object* v_init_3674_, lean_object* v_f_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_){
_start:
{
lean_object* v___x_3681_; 
v___x_3681_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_3673_, v_init_3674_, v_f_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
return v___x_3681_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___boxed(lean_object* v_00_u03c3_3682_, lean_object* v_00_u03b2_3683_, lean_object* v_map_3684_, lean_object* v_init_3685_, lean_object* v_f_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_){
_start:
{
lean_object* v_res_3692_; 
v_res_3692_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(v_00_u03c3_3682_, v_00_u03b2_3683_, v_map_3684_, v_init_3685_, v_f_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_);
lean_dec(v___y_3690_);
lean_dec_ref(v___y_3689_);
lean_dec(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec_ref(v_map_3684_);
return v_res_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(lean_object* v_map_3693_, lean_object* v_f_3694_, lean_object* v_init_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_){
_start:
{
lean_object* v___x_3701_; 
v___x_3701_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3694_, v_map_3693_, v_init_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
return v___x_3701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg___boxed(lean_object* v_map_3702_, lean_object* v_f_3703_, lean_object* v_init_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_){
_start:
{
lean_object* v_res_3710_; 
v_res_3710_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(v_map_3702_, v_f_3703_, v_init_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_);
lean_dec(v___y_3708_);
lean_dec_ref(v___y_3707_);
lean_dec(v___y_3706_);
lean_dec_ref(v___y_3705_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(lean_object* v_00_u03c3_3711_, lean_object* v_00_u03c3_3712_, lean_object* v_00_u03b2_3713_, lean_object* v_map_3714_, lean_object* v_f_3715_, lean_object* v_init_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_){
_start:
{
lean_object* v___x_3722_; 
v___x_3722_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3715_, v_map_3714_, v_init_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
return v___x_3722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___boxed(lean_object* v_00_u03c3_3723_, lean_object* v_00_u03c3_3724_, lean_object* v_00_u03b2_3725_, lean_object* v_map_3726_, lean_object* v_f_3727_, lean_object* v_init_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_){
_start:
{
lean_object* v_res_3734_; 
v_res_3734_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(v_00_u03c3_3723_, v_00_u03c3_3724_, v_00_u03b2_3725_, v_map_3726_, v_f_3727_, v_init_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
lean_dec(v___y_3732_);
lean_dec_ref(v___y_3731_);
lean_dec(v___y_3730_);
lean_dec_ref(v___y_3729_);
return v_res_3734_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(lean_object* v_00_u03c3_3735_, lean_object* v_00_u03c3_3736_, lean_object* v_00_u03b1_3737_, lean_object* v_00_u03b2_3738_, lean_object* v_f_3739_, lean_object* v_x_3740_, lean_object* v_x_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_){
_start:
{
lean_object* v___x_3747_; 
v___x_3747_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3739_, v_x_3740_, v_x_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_);
return v___x_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03c3_3748_, lean_object* v_00_u03c3_3749_, lean_object* v_00_u03b1_3750_, lean_object* v_00_u03b2_3751_, lean_object* v_f_3752_, lean_object* v_x_3753_, lean_object* v_x_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
lean_object* v_res_3760_; 
v_res_3760_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(v_00_u03c3_3748_, v_00_u03c3_3749_, v_00_u03b1_3750_, v_00_u03b2_3751_, v_f_3752_, v_x_3753_, v_x_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
return v_res_3760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(lean_object* v_00_u03b1_3761_, lean_object* v_00_u03b2_3762_, lean_object* v_00_u03c3_3763_, lean_object* v_00_u03c3_3764_, lean_object* v_f_3765_, lean_object* v_as_3766_, size_t v_i_3767_, size_t v_stop_3768_, lean_object* v_b_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_){
_start:
{
lean_object* v___x_3775_; 
v___x_3775_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3765_, v_as_3766_, v_i_3767_, v_stop_3768_, v_b_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_);
return v___x_3775_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b1_3776_, lean_object* v_00_u03b2_3777_, lean_object* v_00_u03c3_3778_, lean_object* v_00_u03c3_3779_, lean_object* v_f_3780_, lean_object* v_as_3781_, lean_object* v_i_3782_, lean_object* v_stop_3783_, lean_object* v_b_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
size_t v_i_boxed_3790_; size_t v_stop_boxed_3791_; lean_object* v_res_3792_; 
v_i_boxed_3790_ = lean_unbox_usize(v_i_3782_);
lean_dec(v_i_3782_);
v_stop_boxed_3791_ = lean_unbox_usize(v_stop_3783_);
lean_dec(v_stop_3783_);
v_res_3792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(v_00_u03b1_3776_, v_00_u03b2_3777_, v_00_u03c3_3778_, v_00_u03c3_3779_, v_f_3780_, v_as_3781_, v_i_boxed_3790_, v_stop_boxed_3791_, v_b_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec(v___y_3786_);
lean_dec_ref(v___y_3785_);
lean_dec_ref(v_as_3781_);
return v_res_3792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(lean_object* v_00_u03c3_3793_, lean_object* v_00_u03c3_3794_, lean_object* v_00_u03b1_3795_, lean_object* v_00_u03b2_3796_, lean_object* v_f_3797_, lean_object* v_keys_3798_, lean_object* v_vals_3799_, lean_object* v_heq_3800_, lean_object* v_i_3801_, lean_object* v_acc_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
lean_object* v___x_3808_; 
v___x_3808_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3797_, v_keys_3798_, v_vals_3799_, v_i_3801_, v_acc_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_);
return v___x_3808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03c3_3809_, lean_object* v_00_u03c3_3810_, lean_object* v_00_u03b1_3811_, lean_object* v_00_u03b2_3812_, lean_object* v_f_3813_, lean_object* v_keys_3814_, lean_object* v_vals_3815_, lean_object* v_heq_3816_, lean_object* v_i_3817_, lean_object* v_acc_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_){
_start:
{
lean_object* v_res_3824_; 
v_res_3824_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(v_00_u03c3_3809_, v_00_u03c3_3810_, v_00_u03b1_3811_, v_00_u03b2_3812_, v_f_3813_, v_keys_3814_, v_vals_3815_, v_heq_3816_, v_i_3817_, v_acc_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_);
lean_dec(v___y_3822_);
lean_dec_ref(v___y_3821_);
lean_dec(v___y_3820_);
lean_dec_ref(v___y_3819_);
lean_dec_ref(v_vals_3815_);
lean_dec_ref(v_keys_3814_);
return v_res_3824_;
}
}
lean_object* runtime_initialize_Lean_DocString(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Tactic_Doc(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Doc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Doc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_DocString(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Parser_Tactic_Doc(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Doc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_DocString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Doc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Doc(builtin);
}
#ifdef __cplusplus
}
#endif
