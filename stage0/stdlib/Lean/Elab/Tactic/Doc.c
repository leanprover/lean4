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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_array_size(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
extern lean_object* l_Lean_LocalContext_empty;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_Doc_tacticNameExt;
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_constants(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_Doc_tacticTagExt;
extern lean_object* l_Lean_Parser_parserExtension;
extern lean_object* l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_MessageData_nestD(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_findDocString_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_Tactic_Doc_getTacticExtensions(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_List_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Doc"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "elabTacticExtension"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 62, 21, 167, 211, 43, 164, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(128, 44, 144, 107, 80, 40, 109, 178)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(17) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__0_value),((lean_object*)(((size_t)(43) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__1_value),((lean_object*)(((size_t)(56) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(17) << 1) | 1)),((lean_object*)(((size_t)(47) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(17) << 1) | 1)),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__3_value),((lean_object*)(((size_t)(47) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__4_value),((lean_object*)(((size_t)(66) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___boxed(lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "elabRegisterTacticTag"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 62, 21, 167, 211, 43, 164, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 30, 89, 153, 147, 186, 30, 23)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(46) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(36) << 1) | 1)),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__0_value),((lean_object*)(((size_t)(46) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__1_value),((lean_object*)(((size_t)(61) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(32) << 1) | 1)),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__3_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__4_value),((lean_object*)(((size_t)(71) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1;
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
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Delab"};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 78, 224, 2, 255, 4, 162, 217)}};
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__2_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__0_value)} };
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__1_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_param___override, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0 = (const lean_object*)&l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__17(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__26(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__26___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "printTacTags"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 6, 105, 20, 120, 144, 238, 207)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "elabPrintTacTags"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(197, 62, 21, 167, 211, 43, 164, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(202, 38, 126, 200, 28, 172, 117, 128)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___boxed(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "Displays all available tactic tags, with documentation.\n"};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(98) << 1) | 1)),((lean_object*)(((size_t)(37) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(130) << 1) | 1)),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__0_value),((lean_object*)(((size_t)(37) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__1_value),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(98) << 1) | 1)),((lean_object*)(((size_t)(41) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(98) << 1) | 1)),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__3_value),((lean_object*)(((size_t)(41) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__4_value),((lean_object*)(((size_t)(57) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___boxed(lean_object*);
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
v___x_26_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
lean_ctor_set(v___x_26_, 1, v___x_25_);
lean_ctor_set(v___x_26_, 2, v___x_25_);
lean_ctor_set(v___x_26_, 3, v___x_24_);
lean_ctor_set(v___x_26_, 4, v___x_24_);
lean_ctor_set(v___x_26_, 5, v___x_24_);
lean_ctor_set(v___x_26_, 6, v___x_24_);
lean_ctor_set(v___x_26_, 7, v___x_24_);
lean_ctor_set(v___x_26_, 8, v___x_24_);
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
lean_dec_ref(v___x_97_);
if (lean_obj_tag(v_val_99_) == 1)
{
uint8_t v_v_100_; 
v_v_100_ = lean_ctor_get_uint8(v_val_99_, 0);
lean_dec_ref(v_val_99_);
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
lean_dec_ref(v___x_151_);
v_macroStack_153_ = lean_ctor_get(v___y_148_, 4);
lean_inc(v_macroStack_153_);
lean_dec_ref(v___y_148_);
v___x_154_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v_msg_147_, v___y_149_);
v_a_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_a_155_);
lean_dec_ref(v___x_154_);
lean_inc(v_macroStack_153_);
v___x_156_ = l_Lean_Elab_getBetterRef(v_a_152_, v_macroStack_153_);
lean_dec(v_a_152_);
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
lean_dec_ref(v___y_148_);
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
lean_object* v_a_186_; lean_object* v_fileName_187_; lean_object* v_fileMap_188_; lean_object* v_currRecDepth_189_; lean_object* v_cmdPos_190_; lean_object* v_macroStack_191_; lean_object* v_quotContext_x3f_192_; lean_object* v_currMacroScope_193_; lean_object* v_snap_x3f_194_; lean_object* v_cancelTk_x3f_195_; uint8_t v_suppressElabErrors_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_205_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_a_186_);
lean_dec_ref(v___x_185_);
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
v_isSharedCheck_205_ = !lean_is_exclusive(v___y_182_);
if (v_isSharedCheck_205_ == 0)
{
lean_object* v_unused_206_; 
v_unused_206_ = lean_ctor_get(v___y_182_, 7);
lean_dec(v_unused_206_);
v___x_198_ = v___y_182_;
v_isShared_199_ = v_isSharedCheck_205_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_cancelTk_x3f_195_);
lean_inc(v_snap_x3f_194_);
lean_inc(v_currMacroScope_193_);
lean_inc(v_quotContext_x3f_192_);
lean_inc(v_macroStack_191_);
lean_inc(v_cmdPos_190_);
lean_inc(v_currRecDepth_189_);
lean_inc(v_fileMap_188_);
lean_inc(v_fileName_187_);
lean_dec(v___y_182_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_205_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v_ref_200_; lean_object* v___x_202_; 
v_ref_200_ = l_Lean_replaceRef(v_ref_180_, v_a_186_);
lean_dec(v_a_186_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 7, v_ref_200_);
v___x_202_ = v___x_198_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_fileName_187_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v_fileMap_188_);
lean_ctor_set(v_reuseFailAlloc_204_, 2, v_currRecDepth_189_);
lean_ctor_set(v_reuseFailAlloc_204_, 3, v_cmdPos_190_);
lean_ctor_set(v_reuseFailAlloc_204_, 4, v_macroStack_191_);
lean_ctor_set(v_reuseFailAlloc_204_, 5, v_quotContext_x3f_192_);
lean_ctor_set(v_reuseFailAlloc_204_, 6, v_currMacroScope_193_);
lean_ctor_set(v_reuseFailAlloc_204_, 7, v_ref_200_);
lean_ctor_set(v_reuseFailAlloc_204_, 8, v_snap_x3f_194_);
lean_ctor_set(v_reuseFailAlloc_204_, 9, v_cancelTk_x3f_195_);
lean_ctor_set_uint8(v_reuseFailAlloc_204_, sizeof(void*)*10, v_suppressElabErrors_196_);
v___x_202_ = v_reuseFailAlloc_204_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v_msg_181_, v___x_202_, v___y_183_);
return v___x_203_;
}
}
}
else
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_214_; 
lean_dec_ref(v___y_182_);
lean_dec_ref(v_msg_181_);
v_a_207_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_214_ == 0)
{
v___x_209_ = v___x_185_;
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_185_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_a_207_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg___boxed(lean_object* v_ref_215_, lean_object* v_msg_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_ref_215_, v_msg_216_, v___y_217_, v___y_218_);
lean_dec(v___y_218_);
lean_dec(v_ref_215_);
return v_res_220_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__5));
v___x_232_ = l_Lean_stringToMessageData(v___x_231_);
return v___x_232_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__11));
v___x_244_ = l_Lean_stringToMessageData(v___x_243_);
return v___x_244_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__13));
v___x_247_ = l_Lean_stringToMessageData(v___x_246_);
return v___x_247_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16(void){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__15));
v___x_250_ = l_Lean_stringToMessageData(v___x_249_);
return v___x_250_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18(void){
_start:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_252_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__17));
v___x_253_ = l_Lean_stringToMessageData(v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension(lean_object* v_x_254_, lean_object* v_a_255_, lean_object* v_a_256_){
_start:
{
lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_258_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4));
lean_inc(v_x_254_);
v___x_259_ = l_Lean_Syntax_isOfKind(v_x_254_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec(v_x_254_);
v___x_260_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6);
v___x_261_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_260_, v_a_255_, v_a_256_);
return v___x_261_;
}
else
{
lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = l_Lean_Syntax_getArg(v_x_254_, v___x_262_);
lean_inc(v___x_263_);
v___x_264_ = l_Lean_Syntax_matchesNull(v___x_263_, v___x_262_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_265_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_263_);
v___x_266_ = l_Lean_Syntax_matchesNull(v___x_263_, v___x_265_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; 
lean_dec(v___x_263_);
lean_dec(v_x_254_);
v___x_267_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6);
v___x_268_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_267_, v_a_255_, v_a_256_);
return v___x_268_;
}
else
{
lean_object* v_docs_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v_docs_269_ = l_Lean_Syntax_getArg(v___x_263_, v___x_262_);
lean_dec(v___x_263_);
v___x_270_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8));
lean_inc(v_docs_269_);
v___x_271_ = l_Lean_Syntax_isOfKind(v_docs_269_, v___x_270_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; lean_object* v___x_273_; 
lean_dec(v_docs_269_);
lean_dec(v_x_254_);
v___x_272_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6);
v___x_273_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_272_, v_a_255_, v_a_256_);
return v___x_273_;
}
else
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_274_ = lean_unsigned_to_nat(2u);
v___x_275_ = l_Lean_Syntax_getArg(v_x_254_, v___x_274_);
lean_dec(v_x_254_);
v___x_276_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10));
lean_inc(v___x_275_);
v___x_277_ = l_Lean_Syntax_isOfKind(v___x_275_, v___x_276_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; lean_object* v___x_279_; 
lean_dec(v___x_275_);
lean_dec(v_docs_269_);
v___x_278_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__6);
v___x_279_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_278_, v_a_255_, v_a_256_);
return v___x_279_;
}
else
{
lean_object* v___x_280_; lean_object* v___f_281_; lean_object* v___x_282_; 
v___x_280_ = lean_box(0);
lean_inc(v___x_275_);
v___f_281_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___lam__0___boxed), 9, 2);
lean_closure_set(v___f_281_, 0, v___x_275_);
lean_closure_set(v___f_281_, 1, v___x_280_);
lean_inc_ref(v_a_255_);
v___x_282_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_281_, v_a_255_, v_a_256_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_349_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_349_ == 0)
{
v___x_285_ = v___x_282_;
v_isShared_286_ = v_isSharedCheck_349_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_282_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_349_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___y_288_; lean_object* v___y_321_; lean_object* v___y_322_; uint8_t v___y_323_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___x_336_; lean_object* v_env_337_; lean_object* v___x_338_; 
v___x_336_ = lean_st_ref_get(v_a_256_);
v_env_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc_ref(v_env_337_);
lean_dec(v___x_336_);
lean_inc(v_a_283_);
v___x_338_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_337_, v_a_283_);
if (lean_obj_tag(v___x_338_) == 1)
{
lean_object* v_val_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
lean_del_object(v___x_285_);
lean_dec(v_docs_269_);
v_val_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_val_339_);
lean_dec_ref(v___x_338_);
v___x_340_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
v___x_341_ = l_Lean_MessageData_ofConstName(v_a_283_, v___x_264_);
v___x_342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_340_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v___x_343_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__16);
v___x_344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_342_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = l_Lean_MessageData_ofConstName(v_val_339_, v___x_264_);
v___x_346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_344_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
v___x_347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
lean_ctor_set(v___x_347_, 1, v___x_340_);
v___x_348_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v___x_275_, v___x_347_, v_a_255_, v_a_256_);
lean_dec(v___x_275_);
return v___x_348_;
}
else
{
lean_dec(v___x_338_);
v___y_331_ = v_a_255_;
v___y_332_ = v_a_256_;
goto v___jp_330_;
}
v___jp_287_:
{
lean_object* v___x_289_; lean_object* v_env_290_; lean_object* v_messages_291_; lean_object* v_scopes_292_; lean_object* v_usedQuotCtxts_293_; lean_object* v_nextMacroScope_294_; lean_object* v_maxRecDepth_295_; lean_object* v_ngen_296_; lean_object* v_auxDeclNGen_297_; lean_object* v_infoState_298_; lean_object* v_traceState_299_; lean_object* v_snapshotTasks_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_319_; 
v___x_289_ = lean_st_ref_take(v___y_288_);
v_env_290_ = lean_ctor_get(v___x_289_, 0);
v_messages_291_ = lean_ctor_get(v___x_289_, 1);
v_scopes_292_ = lean_ctor_get(v___x_289_, 2);
v_usedQuotCtxts_293_ = lean_ctor_get(v___x_289_, 3);
v_nextMacroScope_294_ = lean_ctor_get(v___x_289_, 4);
v_maxRecDepth_295_ = lean_ctor_get(v___x_289_, 5);
v_ngen_296_ = lean_ctor_get(v___x_289_, 6);
v_auxDeclNGen_297_ = lean_ctor_get(v___x_289_, 7);
v_infoState_298_ = lean_ctor_get(v___x_289_, 8);
v_traceState_299_ = lean_ctor_get(v___x_289_, 9);
v_snapshotTasks_300_ = lean_ctor_get(v___x_289_, 10);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_319_ == 0)
{
v___x_302_ = v___x_289_;
v_isShared_303_ = v_isSharedCheck_319_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_snapshotTasks_300_);
lean_inc(v_traceState_299_);
lean_inc(v_infoState_298_);
lean_inc(v_auxDeclNGen_297_);
lean_inc(v_ngen_296_);
lean_inc(v_maxRecDepth_295_);
lean_inc(v_nextMacroScope_294_);
lean_inc(v_usedQuotCtxts_293_);
lean_inc(v_scopes_292_);
lean_inc(v_messages_291_);
lean_inc(v_env_290_);
lean_dec(v___x_289_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_319_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_304_; lean_object* v_toEnvExtension_305_; lean_object* v_asyncMode_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_304_ = l_Lean_Parser_Tactic_Doc_tacticDocExtExt;
v_toEnvExtension_305_ = lean_ctor_get(v___x_304_, 0);
lean_inc_ref(v_toEnvExtension_305_);
v_asyncMode_306_ = lean_ctor_get(v_toEnvExtension_305_, 2);
lean_inc(v_asyncMode_306_);
lean_dec_ref(v_toEnvExtension_305_);
v___x_307_ = l_Lean_TSyntax_getDocString(v_docs_269_);
lean_dec(v_docs_269_);
v___x_308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_308_, 0, v_a_283_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
v___x_309_ = lean_box(0);
v___x_310_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_304_, v_env_290_, v___x_308_, v_asyncMode_306_, v___x_309_);
lean_dec(v_asyncMode_306_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 0, v___x_310_);
v___x_312_ = v___x_302_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_messages_291_);
lean_ctor_set(v_reuseFailAlloc_318_, 2, v_scopes_292_);
lean_ctor_set(v_reuseFailAlloc_318_, 3, v_usedQuotCtxts_293_);
lean_ctor_set(v_reuseFailAlloc_318_, 4, v_nextMacroScope_294_);
lean_ctor_set(v_reuseFailAlloc_318_, 5, v_maxRecDepth_295_);
lean_ctor_set(v_reuseFailAlloc_318_, 6, v_ngen_296_);
lean_ctor_set(v_reuseFailAlloc_318_, 7, v_auxDeclNGen_297_);
lean_ctor_set(v_reuseFailAlloc_318_, 8, v_infoState_298_);
lean_ctor_set(v_reuseFailAlloc_318_, 9, v_traceState_299_);
lean_ctor_set(v_reuseFailAlloc_318_, 10, v_snapshotTasks_300_);
v___x_312_ = v_reuseFailAlloc_318_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_316_; 
v___x_313_ = lean_st_ref_set(v___y_288_, v___x_312_);
v___x_314_ = lean_box(0);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v___x_314_);
v___x_316_ = v___x_285_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_314_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
v___jp_320_:
{
if (v___y_323_ == 0)
{
lean_dec_ref(v___y_321_);
lean_dec(v___x_275_);
v___y_288_ = v___y_322_;
goto v___jp_287_;
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
lean_del_object(v___x_285_);
lean_dec(v_docs_269_);
v___x_324_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
v___x_325_ = l_Lean_MessageData_ofConstName(v_a_283_, v___x_264_);
v___x_326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_324_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
v___x_327_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__14);
v___x_328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_326_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v___x_275_, v___x_328_, v___y_321_, v___y_322_);
lean_dec(v___x_275_);
return v___x_329_;
}
}
v___jp_330_:
{
lean_object* v___x_333_; lean_object* v_env_334_; uint8_t v___x_335_; 
v___x_333_ = lean_st_ref_get(v___y_332_);
v_env_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc_ref(v_env_334_);
lean_dec(v___x_333_);
v___x_335_ = l_Lean_Parser_Tactic_Doc_isTactic(v_env_334_, v_a_283_);
if (v___x_335_ == 0)
{
v___y_321_ = v___y_331_;
v___y_322_ = v___y_332_;
v___y_323_ = v___x_277_;
goto v___jp_320_;
}
else
{
v___y_321_ = v___y_331_;
v___y_322_ = v___y_332_;
v___y_323_ = v___x_264_;
goto v___jp_320_;
}
}
}
}
else
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_357_; 
lean_dec(v___x_275_);
lean_dec(v_docs_269_);
lean_dec_ref(v_a_255_);
v_a_350_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_357_ == 0)
{
v___x_352_ = v___x_282_;
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_282_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_357_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_355_; 
if (v_isShared_353_ == 0)
{
v___x_355_ = v___x_352_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_358_; lean_object* v_cmd_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
lean_dec(v___x_263_);
v___x_358_ = lean_unsigned_to_nat(1u);
v_cmd_359_ = l_Lean_Syntax_getArg(v_x_254_, v___x_358_);
lean_dec(v_x_254_);
v___x_360_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__18);
v___x_361_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_cmd_359_, v___x_360_, v_a_255_, v_a_256_);
lean_dec(v_cmd_359_);
return v___x_361_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed(lean_object* v_x_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension(v_x_362_, v_a_363_, v_a_364_);
lean_dec(v_a_364_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0(lean_object* v_msgData_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v_msgData_367_, v___y_369_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___boxed(lean_object* v_msgData_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0(v_msgData_372_, v___y_373_, v___y_374_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0(lean_object* v_00_u03b1_377_, lean_object* v_msg_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v_msg_378_, v___y_379_, v___y_380_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___boxed(lean_object* v_00_u03b1_383_, lean_object* v_msg_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0(v_00_u03b1_383_, v_msg_384_, v___y_385_, v___y_386_);
lean_dec(v___y_386_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1(lean_object* v_00_u03b1_389_, lean_object* v_ref_390_, lean_object* v_msg_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v___x_395_; 
v___x_395_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_ref_390_, v_msg_391_, v___y_392_, v___y_393_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___boxed(lean_object* v_00_u03b1_396_, lean_object* v_ref_397_, lean_object* v_msg_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1(v_00_u03b1_396_, v_ref_397_, v_msg_398_, v___y_399_, v___y_400_);
lean_dec(v___y_400_);
lean_dec(v_ref_397_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1(lean_object* v_msgData_403_, lean_object* v_macroStack_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___redArg(v_msgData_403_, v_macroStack_404_, v___y_406_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1___boxed(lean_object* v_msgData_409_, lean_object* v_macroStack_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1(v_msgData_409_, v_macroStack_410_, v___y_411_, v___y_412_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1(){
_start:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_426_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_427_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__4));
v___x_428_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_429_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___boxed), 4, 0);
v___x_430_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_426_, v___x_427_, v___x_428_, v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___boxed(lean_object* v_a_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3(){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_459_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1___closed__4));
v___x_460_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___closed__6));
v___x_461_ = l_Lean_addBuiltinDeclarationRanges(v___x_459_, v___x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3___boxed(lean_object* v_a_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
return v_res_463_;
}
}
static lean_object* _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__0));
v___x_466_ = l_Lean_stringToMessageData(v___x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(lean_object* v_stx_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_val_479_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_unsigned_to_nat(1u);
v___x_487_ = l_Lean_Syntax_getArg(v_stx_468_, v___x_486_);
switch(lean_obj_tag(v___x_487_))
{
case 2:
{
lean_object* v_val_488_; 
lean_dec_ref(v___y_469_);
lean_dec(v_stx_468_);
v_val_488_ = lean_ctor_get(v___x_487_, 1);
lean_inc_ref(v_val_488_);
lean_dec_ref(v___x_487_);
v_val_479_ = v_val_488_;
goto v___jp_478_;
}
case 1:
{
lean_object* v_kind_489_; 
v_kind_489_ = lean_ctor_get(v___x_487_, 1);
lean_inc(v_kind_489_);
if (lean_obj_tag(v_kind_489_) == 1)
{
lean_object* v_pre_490_; 
v_pre_490_ = lean_ctor_get(v_kind_489_, 0);
lean_inc(v_pre_490_);
if (lean_obj_tag(v_pre_490_) == 1)
{
lean_object* v_pre_491_; 
v_pre_491_ = lean_ctor_get(v_pre_490_, 0);
lean_inc(v_pre_491_);
if (lean_obj_tag(v_pre_491_) == 1)
{
lean_object* v_pre_492_; 
v_pre_492_ = lean_ctor_get(v_pre_491_, 0);
lean_inc(v_pre_492_);
if (lean_obj_tag(v_pre_492_) == 1)
{
lean_object* v_pre_493_; 
v_pre_493_ = lean_ctor_get(v_pre_492_, 0);
if (lean_obj_tag(v_pre_493_) == 0)
{
lean_object* v_str_494_; lean_object* v_str_495_; lean_object* v_str_496_; lean_object* v_str_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v_str_494_ = lean_ctor_get(v_kind_489_, 1);
lean_inc_ref(v_str_494_);
lean_dec_ref(v_kind_489_);
v_str_495_ = lean_ctor_get(v_pre_490_, 1);
lean_inc_ref(v_str_495_);
lean_dec_ref(v_pre_490_);
v_str_496_ = lean_ctor_get(v_pre_491_, 1);
lean_inc_ref(v_str_496_);
lean_dec_ref(v_pre_491_);
v_str_497_ = lean_ctor_get(v_pre_492_, 1);
lean_inc_ref(v_str_497_);
lean_dec_ref(v_pre_492_);
v___x_498_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0));
v___x_499_ = lean_string_dec_eq(v_str_497_, v___x_498_);
lean_dec_ref(v_str_497_);
if (v___x_499_ == 0)
{
lean_dec_ref(v_str_496_);
lean_dec_ref(v_str_495_);
lean_dec_ref(v_str_494_);
lean_dec_ref(v___x_487_);
goto v___jp_472_;
}
else
{
lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_500_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__1));
v___x_501_ = lean_string_dec_eq(v_str_496_, v___x_500_);
lean_dec_ref(v_str_496_);
if (v___x_501_ == 0)
{
lean_dec_ref(v_str_495_);
lean_dec_ref(v_str_494_);
lean_dec_ref(v___x_487_);
goto v___jp_472_;
}
else
{
lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_502_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__2));
v___x_503_ = lean_string_dec_eq(v_str_495_, v___x_502_);
lean_dec_ref(v_str_495_);
if (v___x_503_ == 0)
{
lean_dec_ref(v_str_494_);
lean_dec_ref(v___x_487_);
goto v___jp_472_;
}
else
{
lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_504_ = ((lean_object*)(l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__2));
v___x_505_ = lean_string_dec_eq(v_str_494_, v___x_504_);
lean_dec_ref(v_str_494_);
if (v___x_505_ == 0)
{
lean_dec_ref(v___x_487_);
goto v___jp_472_;
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_unsigned_to_nat(0u);
v___x_507_ = l_Lean_Syntax_getArg(v___x_487_, v___x_506_);
lean_dec_ref(v___x_487_);
if (lean_obj_tag(v___x_507_) == 2)
{
lean_object* v_val_508_; 
lean_dec_ref(v___y_469_);
lean_dec(v_stx_468_);
v_val_508_ = lean_ctor_get(v___x_507_, 1);
lean_inc_ref(v_val_508_);
lean_dec_ref(v___x_507_);
v_val_479_ = v_val_508_;
goto v___jp_478_;
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
lean_dec(v___x_507_);
v___x_509_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1);
lean_inc(v_stx_468_);
v___x_510_ = l_Lean_MessageData_ofSyntax(v_stx_468_);
v___x_511_ = l_Lean_indentD(v___x_510_);
v___x_512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_509_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
v___x_513_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_stx_468_, v___x_512_, v___y_469_, v___y_470_);
lean_dec(v_stx_468_);
return v___x_513_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_pre_492_);
lean_dec_ref(v_pre_491_);
lean_dec_ref(v_pre_490_);
lean_dec_ref(v_kind_489_);
lean_dec_ref(v___x_487_);
goto v___jp_472_;
}
}
else
{
lean_dec_ref(v_pre_491_);
lean_dec(v_pre_492_);
lean_dec_ref(v_pre_490_);
lean_dec_ref(v_kind_489_);
lean_dec_ref(v___x_487_);
goto v___jp_472_;
}
}
else
{
lean_dec(v_pre_491_);
lean_dec_ref(v_pre_490_);
lean_dec_ref(v_kind_489_);
lean_dec_ref(v___x_487_);
goto v___jp_472_;
}
}
else
{
lean_dec_ref(v_kind_489_);
lean_dec(v_pre_490_);
lean_dec_ref(v___x_487_);
goto v___jp_472_;
}
}
else
{
lean_dec_ref(v___x_487_);
lean_dec(v_kind_489_);
goto v___jp_472_;
}
}
default: 
{
lean_dec(v___x_487_);
goto v___jp_472_;
}
}
v___jp_472_:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_473_ = lean_obj_once(&l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1, &l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1_once, _init_l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___closed__1);
lean_inc(v_stx_468_);
v___x_474_ = l_Lean_MessageData_ofSyntax(v_stx_468_);
v___x_475_ = l_Lean_indentD(v___x_474_);
v___x_476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_473_);
lean_ctor_set(v___x_476_, 1, v___x_475_);
v___x_477_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__1___redArg(v_stx_468_, v___x_476_, v___y_469_, v___y_470_);
lean_dec(v_stx_468_);
return v___x_477_;
}
v___jp_478_:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_480_ = lean_unsigned_to_nat(0u);
v___x_481_ = lean_string_utf8_byte_size(v_val_479_);
v___x_482_ = lean_unsigned_to_nat(2u);
v___x_483_ = lean_nat_sub(v___x_481_, v___x_482_);
v___x_484_ = lean_string_utf8_extract(v_val_479_, v___x_480_, v___x_483_);
lean_dec(v___x_483_);
lean_dec_ref(v_val_479_);
v___x_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
return v___x_485_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0___boxed(lean_object* v_stx_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(v_stx_514_, v___y_515_, v___y_516_);
lean_dec(v___y_516_);
return v_res_518_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__0));
v___x_521_ = l_Lean_stringToMessageData(v___x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(lean_object* v_x_531_, lean_object* v_a_532_, lean_object* v_a_533_){
_start:
{
lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v_a_539_; lean_object* v_doc_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_606_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5));
lean_inc(v_x_531_);
v___x_607_ = l_Lean_Syntax_isOfKind(v_x_531_, v___x_606_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; lean_object* v___x_609_; 
lean_dec(v_x_531_);
v___x_608_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_609_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_608_, v_a_532_, v_a_533_);
return v___x_609_;
}
else
{
lean_object* v___x_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_610_ = lean_unsigned_to_nat(0u);
v___x_611_ = l_Lean_Syntax_getArg(v_x_531_, v___x_610_);
v___x_612_ = l_Lean_Syntax_isNone(v___x_611_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_613_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_611_);
v___x_614_ = l_Lean_Syntax_matchesNull(v___x_611_, v___x_613_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; lean_object* v___x_616_; 
lean_dec(v___x_611_);
lean_dec(v_x_531_);
v___x_615_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_616_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_615_, v_a_532_, v_a_533_);
return v___x_616_;
}
else
{
lean_object* v_doc_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v_doc_617_ = l_Lean_Syntax_getArg(v___x_611_, v___x_610_);
lean_dec(v___x_611_);
v___x_618_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__8));
lean_inc(v_doc_617_);
v___x_619_ = l_Lean_Syntax_isOfKind(v_doc_617_, v___x_618_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; lean_object* v___x_621_; 
lean_dec(v_doc_617_);
lean_dec(v_x_531_);
v___x_620_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_621_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_620_, v_a_532_, v_a_533_);
return v___x_621_;
}
else
{
lean_object* v___x_622_; 
v___x_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_622_, 0, v_doc_617_);
v_doc_572_ = v___x_622_;
v___y_573_ = v_a_532_;
v___y_574_ = v_a_533_;
goto v___jp_571_;
}
}
}
else
{
lean_object* v___x_623_; 
lean_dec(v___x_611_);
v___x_623_ = lean_box(0);
v_doc_572_ = v___x_623_;
v___y_573_ = v_a_532_;
v___y_574_ = v_a_533_;
goto v___jp_571_;
}
}
v___jp_535_:
{
lean_object* v___x_540_; lean_object* v_env_541_; lean_object* v_messages_542_; lean_object* v_scopes_543_; lean_object* v_usedQuotCtxts_544_; lean_object* v_nextMacroScope_545_; lean_object* v_maxRecDepth_546_; lean_object* v_ngen_547_; lean_object* v_auxDeclNGen_548_; lean_object* v_infoState_549_; lean_object* v_traceState_550_; lean_object* v_snapshotTasks_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_570_; 
v___x_540_ = lean_st_ref_take(v___y_538_);
v_env_541_ = lean_ctor_get(v___x_540_, 0);
v_messages_542_ = lean_ctor_get(v___x_540_, 1);
v_scopes_543_ = lean_ctor_get(v___x_540_, 2);
v_usedQuotCtxts_544_ = lean_ctor_get(v___x_540_, 3);
v_nextMacroScope_545_ = lean_ctor_get(v___x_540_, 4);
v_maxRecDepth_546_ = lean_ctor_get(v___x_540_, 5);
v_ngen_547_ = lean_ctor_get(v___x_540_, 6);
v_auxDeclNGen_548_ = lean_ctor_get(v___x_540_, 7);
v_infoState_549_ = lean_ctor_get(v___x_540_, 8);
v_traceState_550_ = lean_ctor_get(v___x_540_, 9);
v_snapshotTasks_551_ = lean_ctor_get(v___x_540_, 10);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_570_ == 0)
{
v___x_553_ = v___x_540_;
v_isShared_554_ = v_isSharedCheck_570_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_snapshotTasks_551_);
lean_inc(v_traceState_550_);
lean_inc(v_infoState_549_);
lean_inc(v_auxDeclNGen_548_);
lean_inc(v_ngen_547_);
lean_inc(v_maxRecDepth_546_);
lean_inc(v_nextMacroScope_545_);
lean_inc(v_usedQuotCtxts_544_);
lean_inc(v_scopes_543_);
lean_inc(v_messages_542_);
lean_inc(v_env_541_);
lean_dec(v___x_540_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_570_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_555_; lean_object* v_toEnvExtension_556_; lean_object* v_asyncMode_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_555_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_556_ = lean_ctor_get(v___x_555_, 0);
lean_inc_ref(v_toEnvExtension_556_);
v_asyncMode_557_ = lean_ctor_get(v_toEnvExtension_556_, 2);
lean_inc(v_asyncMode_557_);
lean_dec_ref(v_toEnvExtension_556_);
v___x_558_ = l_Lean_TSyntax_getId(v___y_536_);
lean_dec(v___y_536_);
v___x_559_ = l_Lean_TSyntax_getString(v___y_537_);
lean_dec(v___y_537_);
v___x_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
lean_ctor_set(v___x_560_, 1, v_a_539_);
v___x_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_558_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v___x_562_ = lean_box(0);
v___x_563_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_555_, v_env_541_, v___x_561_, v_asyncMode_557_, v___x_562_);
lean_dec(v_asyncMode_557_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v___x_563_);
v___x_565_ = v___x_553_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_messages_542_);
lean_ctor_set(v_reuseFailAlloc_569_, 2, v_scopes_543_);
lean_ctor_set(v_reuseFailAlloc_569_, 3, v_usedQuotCtxts_544_);
lean_ctor_set(v_reuseFailAlloc_569_, 4, v_nextMacroScope_545_);
lean_ctor_set(v_reuseFailAlloc_569_, 5, v_maxRecDepth_546_);
lean_ctor_set(v_reuseFailAlloc_569_, 6, v_ngen_547_);
lean_ctor_set(v_reuseFailAlloc_569_, 7, v_auxDeclNGen_548_);
lean_ctor_set(v_reuseFailAlloc_569_, 8, v_infoState_549_);
lean_ctor_set(v_reuseFailAlloc_569_, 9, v_traceState_550_);
lean_ctor_set(v_reuseFailAlloc_569_, 10, v_snapshotTasks_551_);
v___x_565_ = v_reuseFailAlloc_569_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_566_ = lean_st_ref_set(v___y_538_, v___x_565_);
v___x_567_ = lean_box(0);
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
}
}
v___jp_571_:
{
lean_object* v___x_575_; lean_object* v_tag_576_; lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_575_ = lean_unsigned_to_nat(2u);
v_tag_576_ = l_Lean_Syntax_getArg(v_x_531_, v___x_575_);
v___x_577_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__10));
lean_inc(v_tag_576_);
v___x_578_ = l_Lean_Syntax_isOfKind(v_tag_576_, v___x_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; lean_object* v___x_580_; 
lean_dec(v_tag_576_);
lean_dec(v_doc_572_);
lean_dec(v_x_531_);
v___x_579_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_580_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_579_, v___y_573_, v___y_574_);
return v___x_580_;
}
else
{
lean_object* v___x_581_; lean_object* v_user_582_; lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_581_ = lean_unsigned_to_nat(3u);
v_user_582_ = l_Lean_Syntax_getArg(v_x_531_, v___x_581_);
lean_dec(v_x_531_);
v___x_583_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__3));
lean_inc(v_user_582_);
v___x_584_ = l_Lean_Syntax_isOfKind(v_user_582_, v___x_583_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; lean_object* v___x_586_; 
lean_dec(v_user_582_);
lean_dec(v_tag_576_);
lean_dec(v_doc_572_);
v___x_585_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1, &l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1_once, _init_l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__1);
v___x_586_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0___redArg(v___x_585_, v___y_573_, v___y_574_);
return v___x_586_;
}
else
{
if (lean_obj_tag(v_doc_572_) == 0)
{
lean_object* v___x_587_; 
lean_dec_ref(v___y_573_);
v___x_587_ = lean_box(0);
v___y_536_ = v_tag_576_;
v___y_537_ = v_user_582_;
v___y_538_ = v___y_574_;
v_a_539_ = v___x_587_;
goto v___jp_535_;
}
else
{
lean_object* v_val_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_605_; 
v_val_588_ = lean_ctor_get(v_doc_572_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v_doc_572_);
if (v_isSharedCheck_605_ == 0)
{
v___x_590_ = v_doc_572_;
v_isShared_591_ = v_isSharedCheck_605_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_val_588_);
lean_dec(v_doc_572_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_605_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_getDocStringText___at___00Lean_Elab_Tactic_Doc_elabRegisterTacticTag_spec__0(v_val_588_, v___y_573_, v___y_574_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_a_593_; lean_object* v___x_595_; 
v_a_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_a_593_);
lean_dec_ref(v___x_592_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v_a_593_);
v___x_595_ = v___x_590_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_593_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
v___y_536_ = v_tag_576_;
v___y_537_ = v_user_582_;
v___y_538_ = v___y_574_;
v_a_539_ = v___x_595_;
goto v___jp_535_;
}
}
else
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
lean_del_object(v___x_590_);
lean_dec(v_user_582_);
lean_dec(v_tag_576_);
v_a_597_ = lean_ctor_get(v___x_592_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_592_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_592_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_592_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed(lean_object* v_x_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag(v_x_624_, v_a_625_, v_a_626_);
lean_dec(v_a_626_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1(){
_start:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_637_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_638_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___closed__5));
v___x_639_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_640_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___boxed), 4, 0);
v___x_641_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_637_, v___x_638_, v___x_639_, v___x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___boxed(lean_object* v_a_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3(){
_start:
{
lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_670_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1___closed__1));
v___x_671_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___closed__6));
v___x_672_ = l_Lean_addBuiltinDeclarationRanges(v___x_670_, v___x_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3___boxed(lean_object* v_a_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(lean_object* v___x_675_, lean_object* v_x_676_){
_start:
{
if (lean_obj_tag(v_x_676_) == 0)
{
lean_object* v___x_677_; 
v___x_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_675_);
return v___x_677_;
}
else
{
lean_dec_ref(v___x_675_);
lean_inc_ref(v_x_676_);
return v_x_676_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0___boxed(lean_object* v___x_678_, lean_object* v_x_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_678_, v_x_679_);
lean_dec(v_x_679_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(lean_object* v___x_681_, lean_object* v_k_682_, lean_object* v_t_683_){
_start:
{
if (lean_obj_tag(v_t_683_) == 0)
{
lean_object* v_size_684_; lean_object* v_k_685_; lean_object* v_v_686_; lean_object* v_l_687_; lean_object* v_r_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_1014_; 
v_size_684_ = lean_ctor_get(v_t_683_, 0);
v_k_685_ = lean_ctor_get(v_t_683_, 1);
v_v_686_ = lean_ctor_get(v_t_683_, 2);
v_l_687_ = lean_ctor_get(v_t_683_, 3);
v_r_688_ = lean_ctor_get(v_t_683_, 4);
v_isSharedCheck_1014_ = !lean_is_exclusive(v_t_683_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_690_ = v_t_683_;
v_isShared_691_ = v_isSharedCheck_1014_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_r_688_);
lean_inc(v_l_687_);
lean_inc(v_v_686_);
lean_inc(v_k_685_);
lean_inc(v_size_684_);
lean_dec(v_t_683_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_1014_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
uint8_t v___x_692_; 
v___x_692_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_682_, v_k_685_);
switch(v___x_692_)
{
case 0:
{
lean_object* v_impl_693_; lean_object* v___x_694_; 
lean_del_object(v___x_690_);
lean_dec(v_size_684_);
v_impl_693_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_681_, v_k_682_, v_l_687_);
v___x_694_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_685_, v_v_686_, v_impl_693_, v_r_688_);
return v___x_694_;
}
case 1:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
lean_dec(v_k_685_);
v___x_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_695_, 0, v_v_686_);
v___x_696_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_681_, v___x_695_);
lean_dec_ref(v___x_695_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_del_object(v___x_690_);
lean_dec(v_size_684_);
lean_dec(v_k_682_);
if (lean_obj_tag(v_l_687_) == 0)
{
if (lean_obj_tag(v_r_688_) == 0)
{
lean_object* v_size_697_; lean_object* v_k_698_; lean_object* v_v_699_; lean_object* v_l_700_; lean_object* v_r_701_; lean_object* v_size_702_; lean_object* v_k_703_; lean_object* v_v_704_; lean_object* v_l_705_; lean_object* v_r_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v_size_697_ = lean_ctor_get(v_l_687_, 0);
v_k_698_ = lean_ctor_get(v_l_687_, 1);
v_v_699_ = lean_ctor_get(v_l_687_, 2);
v_l_700_ = lean_ctor_get(v_l_687_, 3);
v_r_701_ = lean_ctor_get(v_l_687_, 4);
lean_inc(v_r_701_);
v_size_702_ = lean_ctor_get(v_r_688_, 0);
v_k_703_ = lean_ctor_get(v_r_688_, 1);
v_v_704_ = lean_ctor_get(v_r_688_, 2);
v_l_705_ = lean_ctor_get(v_r_688_, 3);
lean_inc(v_l_705_);
v_r_706_ = lean_ctor_get(v_r_688_, 4);
v___x_707_ = lean_unsigned_to_nat(1u);
v___x_708_ = lean_nat_dec_lt(v_size_697_, v_size_702_);
if (v___x_708_ == 0)
{
lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_844_; 
lean_inc(v_l_700_);
lean_inc(v_v_699_);
lean_inc(v_k_698_);
v_isSharedCheck_844_ = !lean_is_exclusive(v_l_687_);
if (v_isSharedCheck_844_ == 0)
{
lean_object* v_unused_845_; lean_object* v_unused_846_; lean_object* v_unused_847_; lean_object* v_unused_848_; lean_object* v_unused_849_; 
v_unused_845_ = lean_ctor_get(v_l_687_, 4);
lean_dec(v_unused_845_);
v_unused_846_ = lean_ctor_get(v_l_687_, 3);
lean_dec(v_unused_846_);
v_unused_847_ = lean_ctor_get(v_l_687_, 2);
lean_dec(v_unused_847_);
v_unused_848_ = lean_ctor_get(v_l_687_, 1);
lean_dec(v_unused_848_);
v_unused_849_ = lean_ctor_get(v_l_687_, 0);
lean_dec(v_unused_849_);
v___x_710_ = v_l_687_;
v_isShared_711_ = v_isSharedCheck_844_;
goto v_resetjp_709_;
}
else
{
lean_dec(v_l_687_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_844_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; lean_object* v_tree_713_; 
v___x_712_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_698_, v_v_699_, v_l_700_, v_r_701_);
v_tree_713_ = lean_ctor_get(v___x_712_, 2);
lean_inc(v_tree_713_);
if (lean_obj_tag(v_tree_713_) == 0)
{
lean_object* v_k_714_; lean_object* v_v_715_; lean_object* v_size_716_; lean_object* v___x_717_; lean_object* v___x_718_; uint8_t v___x_719_; 
v_k_714_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_k_714_);
v_v_715_ = lean_ctor_get(v___x_712_, 1);
lean_inc(v_v_715_);
lean_dec_ref(v___x_712_);
v_size_716_ = lean_ctor_get(v_tree_713_, 0);
v___x_717_ = lean_unsigned_to_nat(3u);
v___x_718_ = lean_nat_mul(v___x_717_, v_size_716_);
v___x_719_ = lean_nat_dec_lt(v___x_718_, v_size_702_);
lean_dec(v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_723_; 
lean_dec(v_l_705_);
v___x_720_ = lean_nat_add(v___x_707_, v_size_716_);
v___x_721_ = lean_nat_add(v___x_720_, v_size_702_);
lean_dec(v___x_720_);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 4, v_r_688_);
lean_ctor_set(v___x_710_, 3, v_tree_713_);
lean_ctor_set(v___x_710_, 2, v_v_715_);
lean_ctor_set(v___x_710_, 1, v_k_714_);
lean_ctor_set(v___x_710_, 0, v___x_721_);
v___x_723_ = v___x_710_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_721_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_k_714_);
lean_ctor_set(v_reuseFailAlloc_724_, 2, v_v_715_);
lean_ctor_set(v_reuseFailAlloc_724_, 3, v_tree_713_);
lean_ctor_set(v_reuseFailAlloc_724_, 4, v_r_688_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
else
{
lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_779_; 
lean_inc(v_r_706_);
lean_inc(v_v_704_);
lean_inc(v_k_703_);
lean_inc(v_size_702_);
v_isSharedCheck_779_ = !lean_is_exclusive(v_r_688_);
if (v_isSharedCheck_779_ == 0)
{
lean_object* v_unused_780_; lean_object* v_unused_781_; lean_object* v_unused_782_; lean_object* v_unused_783_; lean_object* v_unused_784_; 
v_unused_780_ = lean_ctor_get(v_r_688_, 4);
lean_dec(v_unused_780_);
v_unused_781_ = lean_ctor_get(v_r_688_, 3);
lean_dec(v_unused_781_);
v_unused_782_ = lean_ctor_get(v_r_688_, 2);
lean_dec(v_unused_782_);
v_unused_783_ = lean_ctor_get(v_r_688_, 1);
lean_dec(v_unused_783_);
v_unused_784_ = lean_ctor_get(v_r_688_, 0);
lean_dec(v_unused_784_);
v___x_726_ = v_r_688_;
v_isShared_727_ = v_isSharedCheck_779_;
goto v_resetjp_725_;
}
else
{
lean_dec(v_r_688_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_779_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v_size_728_; lean_object* v_k_729_; lean_object* v_v_730_; lean_object* v_l_731_; lean_object* v_r_732_; lean_object* v_size_733_; lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v_size_728_ = lean_ctor_get(v_l_705_, 0);
v_k_729_ = lean_ctor_get(v_l_705_, 1);
v_v_730_ = lean_ctor_get(v_l_705_, 2);
v_l_731_ = lean_ctor_get(v_l_705_, 3);
v_r_732_ = lean_ctor_get(v_l_705_, 4);
v_size_733_ = lean_ctor_get(v_r_706_, 0);
v___x_734_ = lean_unsigned_to_nat(2u);
v___x_735_ = lean_nat_mul(v___x_734_, v_size_733_);
v___x_736_ = lean_nat_dec_lt(v_size_728_, v___x_735_);
lean_dec(v___x_735_);
if (v___x_736_ == 0)
{
lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_764_; 
lean_inc(v_r_732_);
lean_inc(v_l_731_);
lean_inc(v_v_730_);
lean_inc(v_k_729_);
v_isSharedCheck_764_ = !lean_is_exclusive(v_l_705_);
if (v_isSharedCheck_764_ == 0)
{
lean_object* v_unused_765_; lean_object* v_unused_766_; lean_object* v_unused_767_; lean_object* v_unused_768_; lean_object* v_unused_769_; 
v_unused_765_ = lean_ctor_get(v_l_705_, 4);
lean_dec(v_unused_765_);
v_unused_766_ = lean_ctor_get(v_l_705_, 3);
lean_dec(v_unused_766_);
v_unused_767_ = lean_ctor_get(v_l_705_, 2);
lean_dec(v_unused_767_);
v_unused_768_ = lean_ctor_get(v_l_705_, 1);
lean_dec(v_unused_768_);
v_unused_769_ = lean_ctor_get(v_l_705_, 0);
lean_dec(v_unused_769_);
v___x_738_ = v_l_705_;
v_isShared_739_ = v_isSharedCheck_764_;
goto v_resetjp_737_;
}
else
{
lean_dec(v_l_705_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_764_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___y_743_; lean_object* v___y_744_; lean_object* v___y_745_; lean_object* v___y_754_; 
v___x_740_ = lean_nat_add(v___x_707_, v_size_716_);
v___x_741_ = lean_nat_add(v___x_740_, v_size_702_);
lean_dec(v_size_702_);
if (lean_obj_tag(v_l_731_) == 0)
{
lean_object* v_size_762_; 
v_size_762_ = lean_ctor_get(v_l_731_, 0);
lean_inc(v_size_762_);
v___y_754_ = v_size_762_;
goto v___jp_753_;
}
else
{
lean_object* v___x_763_; 
v___x_763_ = lean_unsigned_to_nat(0u);
v___y_754_ = v___x_763_;
goto v___jp_753_;
}
v___jp_742_:
{
lean_object* v___x_746_; lean_object* v___x_748_; 
v___x_746_ = lean_nat_add(v___y_743_, v___y_745_);
lean_dec(v___y_745_);
lean_dec(v___y_743_);
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 4, v_r_706_);
lean_ctor_set(v___x_738_, 3, v_r_732_);
lean_ctor_set(v___x_738_, 2, v_v_704_);
lean_ctor_set(v___x_738_, 1, v_k_703_);
lean_ctor_set(v___x_738_, 0, v___x_746_);
v___x_748_ = v___x_738_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_746_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_k_703_);
lean_ctor_set(v_reuseFailAlloc_752_, 2, v_v_704_);
lean_ctor_set(v_reuseFailAlloc_752_, 3, v_r_732_);
lean_ctor_set(v_reuseFailAlloc_752_, 4, v_r_706_);
v___x_748_ = v_reuseFailAlloc_752_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_750_; 
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 4, v___x_748_);
lean_ctor_set(v___x_726_, 3, v___y_744_);
lean_ctor_set(v___x_726_, 2, v_v_730_);
lean_ctor_set(v___x_726_, 1, v_k_729_);
lean_ctor_set(v___x_726_, 0, v___x_741_);
v___x_750_ = v___x_726_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_k_729_);
lean_ctor_set(v_reuseFailAlloc_751_, 2, v_v_730_);
lean_ctor_set(v_reuseFailAlloc_751_, 3, v___y_744_);
lean_ctor_set(v_reuseFailAlloc_751_, 4, v___x_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
v___jp_753_:
{
lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_755_ = lean_nat_add(v___x_740_, v___y_754_);
lean_dec(v___y_754_);
lean_dec(v___x_740_);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 4, v_l_731_);
lean_ctor_set(v___x_710_, 3, v_tree_713_);
lean_ctor_set(v___x_710_, 2, v_v_715_);
lean_ctor_set(v___x_710_, 1, v_k_714_);
lean_ctor_set(v___x_710_, 0, v___x_755_);
v___x_757_ = v___x_710_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_k_714_);
lean_ctor_set(v_reuseFailAlloc_761_, 2, v_v_715_);
lean_ctor_set(v_reuseFailAlloc_761_, 3, v_tree_713_);
lean_ctor_set(v_reuseFailAlloc_761_, 4, v_l_731_);
v___x_757_ = v_reuseFailAlloc_761_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_758_; 
v___x_758_ = lean_nat_add(v___x_707_, v_size_733_);
if (lean_obj_tag(v_r_732_) == 0)
{
lean_object* v_size_759_; 
v_size_759_ = lean_ctor_get(v_r_732_, 0);
lean_inc(v_size_759_);
v___y_743_ = v___x_758_;
v___y_744_ = v___x_757_;
v___y_745_ = v_size_759_;
goto v___jp_742_;
}
else
{
lean_object* v___x_760_; 
v___x_760_ = lean_unsigned_to_nat(0u);
v___y_743_ = v___x_758_;
v___y_744_ = v___x_757_;
v___y_745_ = v___x_760_;
goto v___jp_742_;
}
}
}
}
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_774_; 
v___x_770_ = lean_nat_add(v___x_707_, v_size_716_);
v___x_771_ = lean_nat_add(v___x_770_, v_size_702_);
lean_dec(v_size_702_);
v___x_772_ = lean_nat_add(v___x_770_, v_size_728_);
lean_dec(v___x_770_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 4, v_l_705_);
lean_ctor_set(v___x_726_, 3, v_tree_713_);
lean_ctor_set(v___x_726_, 2, v_v_715_);
lean_ctor_set(v___x_726_, 1, v_k_714_);
lean_ctor_set(v___x_726_, 0, v___x_772_);
v___x_774_ = v___x_726_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_772_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_k_714_);
lean_ctor_set(v_reuseFailAlloc_778_, 2, v_v_715_);
lean_ctor_set(v_reuseFailAlloc_778_, 3, v_tree_713_);
lean_ctor_set(v_reuseFailAlloc_778_, 4, v_l_705_);
v___x_774_ = v_reuseFailAlloc_778_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v___x_776_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 4, v_r_706_);
lean_ctor_set(v___x_710_, 3, v___x_774_);
lean_ctor_set(v___x_710_, 2, v_v_704_);
lean_ctor_set(v___x_710_, 1, v_k_703_);
lean_ctor_set(v___x_710_, 0, v___x_771_);
v___x_776_ = v___x_710_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_k_703_);
lean_ctor_set(v_reuseFailAlloc_777_, 2, v_v_704_);
lean_ctor_set(v_reuseFailAlloc_777_, 3, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_777_, 4, v_r_706_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
}
}
else
{
lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_838_; 
lean_inc(v_r_706_);
lean_inc(v_v_704_);
lean_inc(v_k_703_);
lean_inc(v_size_702_);
v_isSharedCheck_838_ = !lean_is_exclusive(v_r_688_);
if (v_isSharedCheck_838_ == 0)
{
lean_object* v_unused_839_; lean_object* v_unused_840_; lean_object* v_unused_841_; lean_object* v_unused_842_; lean_object* v_unused_843_; 
v_unused_839_ = lean_ctor_get(v_r_688_, 4);
lean_dec(v_unused_839_);
v_unused_840_ = lean_ctor_get(v_r_688_, 3);
lean_dec(v_unused_840_);
v_unused_841_ = lean_ctor_get(v_r_688_, 2);
lean_dec(v_unused_841_);
v_unused_842_ = lean_ctor_get(v_r_688_, 1);
lean_dec(v_unused_842_);
v_unused_843_ = lean_ctor_get(v_r_688_, 0);
lean_dec(v_unused_843_);
v___x_786_ = v_r_688_;
v_isShared_787_ = v_isSharedCheck_838_;
goto v_resetjp_785_;
}
else
{
lean_dec(v_r_688_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_838_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
if (lean_obj_tag(v_l_705_) == 0)
{
if (lean_obj_tag(v_r_706_) == 0)
{
lean_object* v_k_788_; lean_object* v_v_789_; lean_object* v_size_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_794_; 
v_k_788_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_k_788_);
v_v_789_ = lean_ctor_get(v___x_712_, 1);
lean_inc(v_v_789_);
lean_dec_ref(v___x_712_);
v_size_790_ = lean_ctor_get(v_l_705_, 0);
v___x_791_ = lean_nat_add(v___x_707_, v_size_702_);
lean_dec(v_size_702_);
v___x_792_ = lean_nat_add(v___x_707_, v_size_790_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 4, v_l_705_);
lean_ctor_set(v___x_786_, 3, v_tree_713_);
lean_ctor_set(v___x_786_, 2, v_v_789_);
lean_ctor_set(v___x_786_, 1, v_k_788_);
lean_ctor_set(v___x_786_, 0, v___x_792_);
v___x_794_ = v___x_786_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_792_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v_k_788_);
lean_ctor_set(v_reuseFailAlloc_798_, 2, v_v_789_);
lean_ctor_set(v_reuseFailAlloc_798_, 3, v_tree_713_);
lean_ctor_set(v_reuseFailAlloc_798_, 4, v_l_705_);
v___x_794_ = v_reuseFailAlloc_798_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
lean_object* v___x_796_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 4, v_r_706_);
lean_ctor_set(v___x_710_, 3, v___x_794_);
lean_ctor_set(v___x_710_, 2, v_v_704_);
lean_ctor_set(v___x_710_, 1, v_k_703_);
lean_ctor_set(v___x_710_, 0, v___x_791_);
v___x_796_ = v___x_710_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_791_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v_k_703_);
lean_ctor_set(v_reuseFailAlloc_797_, 2, v_v_704_);
lean_ctor_set(v_reuseFailAlloc_797_, 3, v___x_794_);
lean_ctor_set(v_reuseFailAlloc_797_, 4, v_r_706_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
else
{
lean_object* v_k_799_; lean_object* v_v_800_; lean_object* v_k_801_; lean_object* v_v_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_816_; 
lean_dec(v_size_702_);
v_k_799_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_k_799_);
v_v_800_ = lean_ctor_get(v___x_712_, 1);
lean_inc(v_v_800_);
lean_dec_ref(v___x_712_);
v_k_801_ = lean_ctor_get(v_l_705_, 1);
v_v_802_ = lean_ctor_get(v_l_705_, 2);
v_isSharedCheck_816_ = !lean_is_exclusive(v_l_705_);
if (v_isSharedCheck_816_ == 0)
{
lean_object* v_unused_817_; lean_object* v_unused_818_; lean_object* v_unused_819_; 
v_unused_817_ = lean_ctor_get(v_l_705_, 4);
lean_dec(v_unused_817_);
v_unused_818_ = lean_ctor_get(v_l_705_, 3);
lean_dec(v_unused_818_);
v_unused_819_ = lean_ctor_get(v_l_705_, 0);
lean_dec(v_unused_819_);
v___x_804_ = v_l_705_;
v_isShared_805_ = v_isSharedCheck_816_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_v_802_);
lean_inc(v_k_801_);
lean_dec(v_l_705_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_816_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; lean_object* v___x_808_; 
v___x_806_ = lean_unsigned_to_nat(3u);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 4, v_r_706_);
lean_ctor_set(v___x_804_, 3, v_r_706_);
lean_ctor_set(v___x_804_, 2, v_v_800_);
lean_ctor_set(v___x_804_, 1, v_k_799_);
lean_ctor_set(v___x_804_, 0, v___x_707_);
v___x_808_ = v___x_804_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_815_, 1, v_k_799_);
lean_ctor_set(v_reuseFailAlloc_815_, 2, v_v_800_);
lean_ctor_set(v_reuseFailAlloc_815_, 3, v_r_706_);
lean_ctor_set(v_reuseFailAlloc_815_, 4, v_r_706_);
v___x_808_ = v_reuseFailAlloc_815_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
lean_object* v___x_810_; 
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 3, v_r_706_);
lean_ctor_set(v___x_786_, 0, v___x_707_);
v___x_810_ = v___x_786_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_814_, 1, v_k_703_);
lean_ctor_set(v_reuseFailAlloc_814_, 2, v_v_704_);
lean_ctor_set(v_reuseFailAlloc_814_, 3, v_r_706_);
lean_ctor_set(v_reuseFailAlloc_814_, 4, v_r_706_);
v___x_810_ = v_reuseFailAlloc_814_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
lean_object* v___x_812_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 4, v___x_810_);
lean_ctor_set(v___x_710_, 3, v___x_808_);
lean_ctor_set(v___x_710_, 2, v_v_802_);
lean_ctor_set(v___x_710_, 1, v_k_801_);
lean_ctor_set(v___x_710_, 0, v___x_806_);
v___x_812_ = v___x_710_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_k_801_);
lean_ctor_set(v_reuseFailAlloc_813_, 2, v_v_802_);
lean_ctor_set(v_reuseFailAlloc_813_, 3, v___x_808_);
lean_ctor_set(v_reuseFailAlloc_813_, 4, v___x_810_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_706_) == 0)
{
lean_object* v_k_820_; lean_object* v_v_821_; lean_object* v___x_822_; lean_object* v___x_824_; 
lean_dec(v_size_702_);
v_k_820_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_k_820_);
v_v_821_ = lean_ctor_get(v___x_712_, 1);
lean_inc(v_v_821_);
lean_dec_ref(v___x_712_);
v___x_822_ = lean_unsigned_to_nat(3u);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 4, v_l_705_);
lean_ctor_set(v___x_786_, 2, v_v_821_);
lean_ctor_set(v___x_786_, 1, v_k_820_);
lean_ctor_set(v___x_786_, 0, v___x_707_);
v___x_824_ = v___x_786_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_828_, 1, v_k_820_);
lean_ctor_set(v_reuseFailAlloc_828_, 2, v_v_821_);
lean_ctor_set(v_reuseFailAlloc_828_, 3, v_l_705_);
lean_ctor_set(v_reuseFailAlloc_828_, 4, v_l_705_);
v___x_824_ = v_reuseFailAlloc_828_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
lean_object* v___x_826_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 4, v_r_706_);
lean_ctor_set(v___x_710_, 3, v___x_824_);
lean_ctor_set(v___x_710_, 2, v_v_704_);
lean_ctor_set(v___x_710_, 1, v_k_703_);
lean_ctor_set(v___x_710_, 0, v___x_822_);
v___x_826_ = v___x_710_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v___x_822_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v_k_703_);
lean_ctor_set(v_reuseFailAlloc_827_, 2, v_v_704_);
lean_ctor_set(v_reuseFailAlloc_827_, 3, v___x_824_);
lean_ctor_set(v_reuseFailAlloc_827_, 4, v_r_706_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
else
{
lean_object* v_k_829_; lean_object* v_v_830_; lean_object* v___x_832_; 
v_k_829_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_k_829_);
v_v_830_ = lean_ctor_get(v___x_712_, 1);
lean_inc(v_v_830_);
lean_dec_ref(v___x_712_);
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 3, v_r_706_);
v___x_832_ = v___x_786_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_size_702_);
lean_ctor_set(v_reuseFailAlloc_837_, 1, v_k_703_);
lean_ctor_set(v_reuseFailAlloc_837_, 2, v_v_704_);
lean_ctor_set(v_reuseFailAlloc_837_, 3, v_r_706_);
lean_ctor_set(v_reuseFailAlloc_837_, 4, v_r_706_);
v___x_832_ = v_reuseFailAlloc_837_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_833_ = lean_unsigned_to_nat(2u);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 4, v___x_832_);
lean_ctor_set(v___x_710_, 3, v_r_706_);
lean_ctor_set(v___x_710_, 2, v_v_830_);
lean_ctor_set(v___x_710_, 1, v_k_829_);
lean_ctor_set(v___x_710_, 0, v___x_833_);
v___x_835_ = v___x_710_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_833_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_k_829_);
lean_ctor_set(v_reuseFailAlloc_836_, 2, v_v_830_);
lean_ctor_set(v_reuseFailAlloc_836_, 3, v_r_706_);
lean_ctor_set(v_reuseFailAlloc_836_, 4, v___x_832_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
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
lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_1002_; 
lean_inc(v_r_706_);
lean_inc(v_v_704_);
lean_inc(v_k_703_);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_r_688_);
if (v_isSharedCheck_1002_ == 0)
{
lean_object* v_unused_1003_; lean_object* v_unused_1004_; lean_object* v_unused_1005_; lean_object* v_unused_1006_; lean_object* v_unused_1007_; 
v_unused_1003_ = lean_ctor_get(v_r_688_, 4);
lean_dec(v_unused_1003_);
v_unused_1004_ = lean_ctor_get(v_r_688_, 3);
lean_dec(v_unused_1004_);
v_unused_1005_ = lean_ctor_get(v_r_688_, 2);
lean_dec(v_unused_1005_);
v_unused_1006_ = lean_ctor_get(v_r_688_, 1);
lean_dec(v_unused_1006_);
v_unused_1007_ = lean_ctor_get(v_r_688_, 0);
lean_dec(v_unused_1007_);
v___x_851_ = v_r_688_;
v_isShared_852_ = v_isSharedCheck_1002_;
goto v_resetjp_850_;
}
else
{
lean_dec(v_r_688_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_1002_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; lean_object* v_tree_854_; 
v___x_853_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_703_, v_v_704_, v_l_705_, v_r_706_);
v_tree_854_ = lean_ctor_get(v___x_853_, 2);
lean_inc(v_tree_854_);
if (lean_obj_tag(v_tree_854_) == 0)
{
lean_object* v_k_855_; lean_object* v_v_856_; lean_object* v_size_857_; lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v_k_855_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_k_855_);
v_v_856_ = lean_ctor_get(v___x_853_, 1);
lean_inc(v_v_856_);
lean_dec_ref(v___x_853_);
v_size_857_ = lean_ctor_get(v_tree_854_, 0);
v___x_858_ = lean_unsigned_to_nat(3u);
v___x_859_ = lean_nat_mul(v___x_858_, v_size_857_);
v___x_860_ = lean_nat_dec_lt(v___x_859_, v_size_697_);
lean_dec(v___x_859_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_864_; 
lean_dec(v_r_701_);
v___x_861_ = lean_nat_add(v___x_707_, v_size_697_);
v___x_862_ = lean_nat_add(v___x_861_, v_size_857_);
lean_dec(v___x_861_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 4, v_tree_854_);
lean_ctor_set(v___x_851_, 3, v_l_687_);
lean_ctor_set(v___x_851_, 2, v_v_856_);
lean_ctor_set(v___x_851_, 1, v_k_855_);
lean_ctor_set(v___x_851_, 0, v___x_862_);
v___x_864_ = v___x_851_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_k_855_);
lean_ctor_set(v_reuseFailAlloc_865_, 2, v_v_856_);
lean_ctor_set(v_reuseFailAlloc_865_, 3, v_l_687_);
lean_ctor_set(v_reuseFailAlloc_865_, 4, v_tree_854_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
else
{
lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_931_; 
lean_inc(v_l_700_);
lean_inc(v_v_699_);
lean_inc(v_k_698_);
lean_inc(v_size_697_);
v_isSharedCheck_931_ = !lean_is_exclusive(v_l_687_);
if (v_isSharedCheck_931_ == 0)
{
lean_object* v_unused_932_; lean_object* v_unused_933_; lean_object* v_unused_934_; lean_object* v_unused_935_; lean_object* v_unused_936_; 
v_unused_932_ = lean_ctor_get(v_l_687_, 4);
lean_dec(v_unused_932_);
v_unused_933_ = lean_ctor_get(v_l_687_, 3);
lean_dec(v_unused_933_);
v_unused_934_ = lean_ctor_get(v_l_687_, 2);
lean_dec(v_unused_934_);
v_unused_935_ = lean_ctor_get(v_l_687_, 1);
lean_dec(v_unused_935_);
v_unused_936_ = lean_ctor_get(v_l_687_, 0);
lean_dec(v_unused_936_);
v___x_867_ = v_l_687_;
v_isShared_868_ = v_isSharedCheck_931_;
goto v_resetjp_866_;
}
else
{
lean_dec(v_l_687_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_931_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v_size_869_; lean_object* v_size_870_; lean_object* v_k_871_; lean_object* v_v_872_; lean_object* v_l_873_; lean_object* v_r_874_; lean_object* v___x_875_; lean_object* v___x_876_; uint8_t v___x_877_; 
v_size_869_ = lean_ctor_get(v_l_700_, 0);
v_size_870_ = lean_ctor_get(v_r_701_, 0);
v_k_871_ = lean_ctor_get(v_r_701_, 1);
v_v_872_ = lean_ctor_get(v_r_701_, 2);
v_l_873_ = lean_ctor_get(v_r_701_, 3);
v_r_874_ = lean_ctor_get(v_r_701_, 4);
v___x_875_ = lean_unsigned_to_nat(2u);
v___x_876_ = lean_nat_mul(v___x_875_, v_size_869_);
v___x_877_ = lean_nat_dec_lt(v_size_870_, v___x_876_);
lean_dec(v___x_876_);
if (v___x_877_ == 0)
{
lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_915_; 
lean_inc(v_r_874_);
lean_inc(v_l_873_);
lean_inc(v_v_872_);
lean_inc(v_k_871_);
lean_del_object(v___x_867_);
v_isSharedCheck_915_ = !lean_is_exclusive(v_r_701_);
if (v_isSharedCheck_915_ == 0)
{
lean_object* v_unused_916_; lean_object* v_unused_917_; lean_object* v_unused_918_; lean_object* v_unused_919_; lean_object* v_unused_920_; 
v_unused_916_ = lean_ctor_get(v_r_701_, 4);
lean_dec(v_unused_916_);
v_unused_917_ = lean_ctor_get(v_r_701_, 3);
lean_dec(v_unused_917_);
v_unused_918_ = lean_ctor_get(v_r_701_, 2);
lean_dec(v_unused_918_);
v_unused_919_ = lean_ctor_get(v_r_701_, 1);
lean_dec(v_unused_919_);
v_unused_920_ = lean_ctor_get(v_r_701_, 0);
lean_dec(v_unused_920_);
v___x_879_ = v_r_701_;
v_isShared_880_ = v_isSharedCheck_915_;
goto v_resetjp_878_;
}
else
{
lean_dec(v_r_701_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_915_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___x_903_; lean_object* v___y_905_; 
v___x_881_ = lean_nat_add(v___x_707_, v_size_697_);
lean_dec(v_size_697_);
v___x_882_ = lean_nat_add(v___x_881_, v_size_857_);
lean_dec(v___x_881_);
v___x_903_ = lean_nat_add(v___x_707_, v_size_869_);
if (lean_obj_tag(v_l_873_) == 0)
{
lean_object* v_size_913_; 
v_size_913_ = lean_ctor_get(v_l_873_, 0);
lean_inc(v_size_913_);
v___y_905_ = v_size_913_;
goto v___jp_904_;
}
else
{
lean_object* v___x_914_; 
v___x_914_ = lean_unsigned_to_nat(0u);
v___y_905_ = v___x_914_;
goto v___jp_904_;
}
v___jp_883_:
{
lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_887_ = lean_nat_add(v___y_884_, v___y_886_);
lean_dec(v___y_886_);
lean_dec(v___y_884_);
lean_inc_ref(v_tree_854_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 4, v_tree_854_);
lean_ctor_set(v___x_879_, 3, v_r_874_);
lean_ctor_set(v___x_879_, 2, v_v_856_);
lean_ctor_set(v___x_879_, 1, v_k_855_);
lean_ctor_set(v___x_879_, 0, v___x_887_);
v___x_889_ = v___x_879_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_k_855_);
lean_ctor_set(v_reuseFailAlloc_902_, 2, v_v_856_);
lean_ctor_set(v_reuseFailAlloc_902_, 3, v_r_874_);
lean_ctor_set(v_reuseFailAlloc_902_, 4, v_tree_854_);
v___x_889_ = v_reuseFailAlloc_902_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
v_isSharedCheck_896_ = !lean_is_exclusive(v_tree_854_);
if (v_isSharedCheck_896_ == 0)
{
lean_object* v_unused_897_; lean_object* v_unused_898_; lean_object* v_unused_899_; lean_object* v_unused_900_; lean_object* v_unused_901_; 
v_unused_897_ = lean_ctor_get(v_tree_854_, 4);
lean_dec(v_unused_897_);
v_unused_898_ = lean_ctor_get(v_tree_854_, 3);
lean_dec(v_unused_898_);
v_unused_899_ = lean_ctor_get(v_tree_854_, 2);
lean_dec(v_unused_899_);
v_unused_900_ = lean_ctor_get(v_tree_854_, 1);
lean_dec(v_unused_900_);
v_unused_901_ = lean_ctor_get(v_tree_854_, 0);
lean_dec(v_unused_901_);
v___x_891_ = v_tree_854_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_dec(v_tree_854_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 4, v___x_889_);
lean_ctor_set(v___x_891_, 3, v___y_885_);
lean_ctor_set(v___x_891_, 2, v_v_872_);
lean_ctor_set(v___x_891_, 1, v_k_871_);
lean_ctor_set(v___x_891_, 0, v___x_882_);
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_k_871_);
lean_ctor_set(v_reuseFailAlloc_895_, 2, v_v_872_);
lean_ctor_set(v_reuseFailAlloc_895_, 3, v___y_885_);
lean_ctor_set(v_reuseFailAlloc_895_, 4, v___x_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
v___jp_904_:
{
lean_object* v___x_906_; lean_object* v___x_908_; 
v___x_906_ = lean_nat_add(v___x_903_, v___y_905_);
lean_dec(v___y_905_);
lean_dec(v___x_903_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 4, v_l_873_);
lean_ctor_set(v___x_851_, 3, v_l_700_);
lean_ctor_set(v___x_851_, 2, v_v_699_);
lean_ctor_set(v___x_851_, 1, v_k_698_);
lean_ctor_set(v___x_851_, 0, v___x_906_);
v___x_908_ = v___x_851_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v_k_698_);
lean_ctor_set(v_reuseFailAlloc_912_, 2, v_v_699_);
lean_ctor_set(v_reuseFailAlloc_912_, 3, v_l_700_);
lean_ctor_set(v_reuseFailAlloc_912_, 4, v_l_873_);
v___x_908_ = v_reuseFailAlloc_912_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_909_; 
v___x_909_ = lean_nat_add(v___x_707_, v_size_857_);
if (lean_obj_tag(v_r_874_) == 0)
{
lean_object* v_size_910_; 
v_size_910_ = lean_ctor_get(v_r_874_, 0);
lean_inc(v_size_910_);
v___y_884_ = v___x_909_;
v___y_885_ = v___x_908_;
v___y_886_ = v_size_910_;
goto v___jp_883_;
}
else
{
lean_object* v___x_911_; 
v___x_911_ = lean_unsigned_to_nat(0u);
v___y_884_ = v___x_909_;
v___y_885_ = v___x_908_;
v___y_886_ = v___x_911_;
goto v___jp_883_;
}
}
}
}
}
else
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_926_; 
v___x_921_ = lean_nat_add(v___x_707_, v_size_697_);
lean_dec(v_size_697_);
v___x_922_ = lean_nat_add(v___x_921_, v_size_857_);
lean_dec(v___x_921_);
v___x_923_ = lean_nat_add(v___x_707_, v_size_857_);
v___x_924_ = lean_nat_add(v___x_923_, v_size_870_);
lean_dec(v___x_923_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 4, v_tree_854_);
lean_ctor_set(v___x_851_, 3, v_r_701_);
lean_ctor_set(v___x_851_, 2, v_v_856_);
lean_ctor_set(v___x_851_, 1, v_k_855_);
lean_ctor_set(v___x_851_, 0, v___x_924_);
v___x_926_ = v___x_851_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v_k_855_);
lean_ctor_set(v_reuseFailAlloc_930_, 2, v_v_856_);
lean_ctor_set(v_reuseFailAlloc_930_, 3, v_r_701_);
lean_ctor_set(v_reuseFailAlloc_930_, 4, v_tree_854_);
v___x_926_ = v_reuseFailAlloc_930_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
lean_object* v___x_928_; 
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 4, v___x_926_);
lean_ctor_set(v___x_867_, 0, v___x_922_);
v___x_928_ = v___x_867_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_922_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_k_698_);
lean_ctor_set(v_reuseFailAlloc_929_, 2, v_v_699_);
lean_ctor_set(v_reuseFailAlloc_929_, 3, v_l_700_);
lean_ctor_set(v_reuseFailAlloc_929_, 4, v___x_926_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_700_) == 0)
{
lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_960_; 
lean_inc_ref(v_l_700_);
lean_inc(v_v_699_);
lean_inc(v_k_698_);
lean_inc(v_size_697_);
v_isSharedCheck_960_ = !lean_is_exclusive(v_l_687_);
if (v_isSharedCheck_960_ == 0)
{
lean_object* v_unused_961_; lean_object* v_unused_962_; lean_object* v_unused_963_; lean_object* v_unused_964_; lean_object* v_unused_965_; 
v_unused_961_ = lean_ctor_get(v_l_687_, 4);
lean_dec(v_unused_961_);
v_unused_962_ = lean_ctor_get(v_l_687_, 3);
lean_dec(v_unused_962_);
v_unused_963_ = lean_ctor_get(v_l_687_, 2);
lean_dec(v_unused_963_);
v_unused_964_ = lean_ctor_get(v_l_687_, 1);
lean_dec(v_unused_964_);
v_unused_965_ = lean_ctor_get(v_l_687_, 0);
lean_dec(v_unused_965_);
v___x_938_ = v_l_687_;
v_isShared_939_ = v_isSharedCheck_960_;
goto v_resetjp_937_;
}
else
{
lean_dec(v_l_687_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_960_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
if (lean_obj_tag(v_r_701_) == 0)
{
lean_object* v_k_940_; lean_object* v_v_941_; lean_object* v_size_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
v_k_940_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_k_940_);
v_v_941_ = lean_ctor_get(v___x_853_, 1);
lean_inc(v_v_941_);
lean_dec_ref(v___x_853_);
v_size_942_ = lean_ctor_get(v_r_701_, 0);
v___x_943_ = lean_nat_add(v___x_707_, v_size_697_);
lean_dec(v_size_697_);
v___x_944_ = lean_nat_add(v___x_707_, v_size_942_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 4, v_tree_854_);
lean_ctor_set(v___x_851_, 3, v_r_701_);
lean_ctor_set(v___x_851_, 2, v_v_941_);
lean_ctor_set(v___x_851_, 1, v_k_940_);
lean_ctor_set(v___x_851_, 0, v___x_944_);
v___x_946_ = v___x_851_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_k_940_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_v_941_);
lean_ctor_set(v_reuseFailAlloc_950_, 3, v_r_701_);
lean_ctor_set(v_reuseFailAlloc_950_, 4, v_tree_854_);
v___x_946_ = v_reuseFailAlloc_950_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_948_; 
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 4, v___x_946_);
lean_ctor_set(v___x_938_, 0, v___x_943_);
v___x_948_ = v___x_938_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_943_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v_k_698_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v_v_699_);
lean_ctor_set(v_reuseFailAlloc_949_, 3, v_l_700_);
lean_ctor_set(v_reuseFailAlloc_949_, 4, v___x_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
else
{
lean_object* v_k_951_; lean_object* v_v_952_; lean_object* v___x_953_; lean_object* v___x_955_; 
lean_dec(v_size_697_);
v_k_951_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_k_951_);
v_v_952_ = lean_ctor_get(v___x_853_, 1);
lean_inc(v_v_952_);
lean_dec_ref(v___x_853_);
v___x_953_ = lean_unsigned_to_nat(3u);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 4, v_r_701_);
lean_ctor_set(v___x_851_, 3, v_r_701_);
lean_ctor_set(v___x_851_, 2, v_v_952_);
lean_ctor_set(v___x_851_, 1, v_k_951_);
lean_ctor_set(v___x_851_, 0, v___x_707_);
v___x_955_ = v___x_851_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v_k_951_);
lean_ctor_set(v_reuseFailAlloc_959_, 2, v_v_952_);
lean_ctor_set(v_reuseFailAlloc_959_, 3, v_r_701_);
lean_ctor_set(v_reuseFailAlloc_959_, 4, v_r_701_);
v___x_955_ = v_reuseFailAlloc_959_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
lean_object* v___x_957_; 
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 4, v___x_955_);
lean_ctor_set(v___x_938_, 0, v___x_953_);
v___x_957_ = v___x_938_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_958_, 1, v_k_698_);
lean_ctor_set(v_reuseFailAlloc_958_, 2, v_v_699_);
lean_ctor_set(v_reuseFailAlloc_958_, 3, v_l_700_);
lean_ctor_set(v_reuseFailAlloc_958_, 4, v___x_955_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_701_) == 0)
{
lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_990_; 
lean_inc(v_l_700_);
lean_inc(v_v_699_);
lean_inc(v_k_698_);
v_isSharedCheck_990_ = !lean_is_exclusive(v_l_687_);
if (v_isSharedCheck_990_ == 0)
{
lean_object* v_unused_991_; lean_object* v_unused_992_; lean_object* v_unused_993_; lean_object* v_unused_994_; lean_object* v_unused_995_; 
v_unused_991_ = lean_ctor_get(v_l_687_, 4);
lean_dec(v_unused_991_);
v_unused_992_ = lean_ctor_get(v_l_687_, 3);
lean_dec(v_unused_992_);
v_unused_993_ = lean_ctor_get(v_l_687_, 2);
lean_dec(v_unused_993_);
v_unused_994_ = lean_ctor_get(v_l_687_, 1);
lean_dec(v_unused_994_);
v_unused_995_ = lean_ctor_get(v_l_687_, 0);
lean_dec(v_unused_995_);
v___x_967_ = v_l_687_;
v_isShared_968_ = v_isSharedCheck_990_;
goto v_resetjp_966_;
}
else
{
lean_dec(v_l_687_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_990_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v_k_969_; lean_object* v_v_970_; lean_object* v_k_971_; lean_object* v_v_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_986_; 
v_k_969_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_k_969_);
v_v_970_ = lean_ctor_get(v___x_853_, 1);
lean_inc(v_v_970_);
lean_dec_ref(v___x_853_);
v_k_971_ = lean_ctor_get(v_r_701_, 1);
v_v_972_ = lean_ctor_get(v_r_701_, 2);
v_isSharedCheck_986_ = !lean_is_exclusive(v_r_701_);
if (v_isSharedCheck_986_ == 0)
{
lean_object* v_unused_987_; lean_object* v_unused_988_; lean_object* v_unused_989_; 
v_unused_987_ = lean_ctor_get(v_r_701_, 4);
lean_dec(v_unused_987_);
v_unused_988_ = lean_ctor_get(v_r_701_, 3);
lean_dec(v_unused_988_);
v_unused_989_ = lean_ctor_get(v_r_701_, 0);
lean_dec(v_unused_989_);
v___x_974_ = v_r_701_;
v_isShared_975_ = v_isSharedCheck_986_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_v_972_);
lean_inc(v_k_971_);
lean_dec(v_r_701_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_986_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_976_; lean_object* v___x_978_; 
v___x_976_ = lean_unsigned_to_nat(3u);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 4, v_l_700_);
lean_ctor_set(v___x_974_, 3, v_l_700_);
lean_ctor_set(v___x_974_, 2, v_v_699_);
lean_ctor_set(v___x_974_, 1, v_k_698_);
lean_ctor_set(v___x_974_, 0, v___x_707_);
v___x_978_ = v___x_974_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v_k_698_);
lean_ctor_set(v_reuseFailAlloc_985_, 2, v_v_699_);
lean_ctor_set(v_reuseFailAlloc_985_, 3, v_l_700_);
lean_ctor_set(v_reuseFailAlloc_985_, 4, v_l_700_);
v___x_978_ = v_reuseFailAlloc_985_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
lean_object* v___x_980_; 
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 4, v_l_700_);
lean_ctor_set(v___x_851_, 3, v_l_700_);
lean_ctor_set(v___x_851_, 2, v_v_970_);
lean_ctor_set(v___x_851_, 1, v_k_969_);
lean_ctor_set(v___x_851_, 0, v___x_707_);
v___x_980_ = v___x_851_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v_k_969_);
lean_ctor_set(v_reuseFailAlloc_984_, 2, v_v_970_);
lean_ctor_set(v_reuseFailAlloc_984_, 3, v_l_700_);
lean_ctor_set(v_reuseFailAlloc_984_, 4, v_l_700_);
v___x_980_ = v_reuseFailAlloc_984_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_982_; 
if (v_isShared_968_ == 0)
{
lean_ctor_set(v___x_967_, 4, v___x_980_);
lean_ctor_set(v___x_967_, 3, v___x_978_);
lean_ctor_set(v___x_967_, 2, v_v_972_);
lean_ctor_set(v___x_967_, 1, v_k_971_);
lean_ctor_set(v___x_967_, 0, v___x_976_);
v___x_982_ = v___x_967_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_976_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v_k_971_);
lean_ctor_set(v_reuseFailAlloc_983_, 2, v_v_972_);
lean_ctor_set(v_reuseFailAlloc_983_, 3, v___x_978_);
lean_ctor_set(v_reuseFailAlloc_983_, 4, v___x_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
}
}
else
{
lean_object* v_k_996_; lean_object* v_v_997_; lean_object* v___x_998_; lean_object* v___x_1000_; 
v_k_996_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_k_996_);
v_v_997_ = lean_ctor_get(v___x_853_, 1);
lean_inc(v_v_997_);
lean_dec_ref(v___x_853_);
v___x_998_ = lean_unsigned_to_nat(2u);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 4, v_r_701_);
lean_ctor_set(v___x_851_, 3, v_l_687_);
lean_ctor_set(v___x_851_, 2, v_v_997_);
lean_ctor_set(v___x_851_, 1, v_k_996_);
lean_ctor_set(v___x_851_, 0, v___x_998_);
v___x_1000_ = v___x_851_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_998_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_k_996_);
lean_ctor_set(v_reuseFailAlloc_1001_, 2, v_v_997_);
lean_ctor_set(v_reuseFailAlloc_1001_, 3, v_l_687_);
lean_ctor_set(v_reuseFailAlloc_1001_, 4, v_r_701_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
}
}
}
else
{
return v_l_687_;
}
}
else
{
return v_r_688_;
}
}
else
{
lean_object* v_val_1008_; lean_object* v___x_1010_; 
v_val_1008_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_val_1008_);
lean_dec_ref(v___x_696_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 2, v_val_1008_);
lean_ctor_set(v___x_690_, 1, v_k_682_);
v___x_1010_ = v___x_690_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_size_684_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_k_682_);
lean_ctor_set(v_reuseFailAlloc_1011_, 2, v_val_1008_);
lean_ctor_set(v_reuseFailAlloc_1011_, 3, v_l_687_);
lean_ctor_set(v_reuseFailAlloc_1011_, 4, v_r_688_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
default: 
{
lean_object* v_impl_1012_; lean_object* v___x_1013_; 
lean_del_object(v___x_690_);
lean_dec(v_size_684_);
v_impl_1012_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_681_, v_k_682_, v_r_688_);
v___x_1013_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_685_, v_v_686_, v_l_687_, v_impl_1012_);
return v___x_1013_;
}
}
}
}
else
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = lean_box(0);
v___x_1016_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg___lam__0(v___x_681_, v___x_1015_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_dec(v_k_682_);
return v_t_683_;
}
else
{
lean_object* v_val_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v_val_1017_ = lean_ctor_get(v___x_1016_, 0);
lean_inc(v_val_1017_);
lean_dec_ref(v___x_1016_);
v___x_1018_ = lean_unsigned_to_nat(1u);
v___x_1019_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
lean_ctor_set(v___x_1019_, 1, v_k_682_);
lean_ctor_set(v___x_1019_, 2, v_val_1017_);
lean_ctor_set(v___x_1019_, 3, v_t_683_);
lean_ctor_set(v___x_1019_, 4, v_t_683_);
return v___x_1019_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1020_, lean_object* v_i_1021_, lean_object* v_k_1022_){
_start:
{
lean_object* v___x_1023_; uint8_t v___x_1024_; 
v___x_1023_ = lean_array_get_size(v_keys_1020_);
v___x_1024_ = lean_nat_dec_lt(v_i_1021_, v___x_1023_);
if (v___x_1024_ == 0)
{
lean_dec(v_i_1021_);
return v___x_1024_;
}
else
{
lean_object* v_k_x27_1025_; uint8_t v___x_1026_; 
v_k_x27_1025_ = lean_array_fget_borrowed(v_keys_1020_, v_i_1021_);
v___x_1026_ = lean_name_eq(v_k_1022_, v_k_x27_1025_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = lean_unsigned_to_nat(1u);
v___x_1028_ = lean_nat_add(v_i_1021_, v___x_1027_);
lean_dec(v_i_1021_);
v_i_1021_ = v___x_1028_;
goto _start;
}
else
{
lean_dec(v_i_1021_);
return v___x_1026_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1030_, lean_object* v_i_1031_, lean_object* v_k_1032_){
_start:
{
uint8_t v_res_1033_; lean_object* v_r_1034_; 
v_res_1033_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_1030_, v_i_1031_, v_k_1032_);
lean_dec(v_k_1032_);
lean_dec_ref(v_keys_1030_);
v_r_1034_ = lean_box(v_res_1033_);
return v_r_1034_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1035_; size_t v___x_1036_; size_t v___x_1037_; 
v___x_1035_ = ((size_t)5ULL);
v___x_1036_ = ((size_t)1ULL);
v___x_1037_ = lean_usize_shift_left(v___x_1036_, v___x_1035_);
return v___x_1037_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1038_; size_t v___x_1039_; size_t v___x_1040_; 
v___x_1038_ = ((size_t)1ULL);
v___x_1039_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0);
v___x_1040_ = lean_usize_sub(v___x_1039_, v___x_1038_);
return v___x_1040_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(lean_object* v_x_1041_, size_t v_x_1042_, lean_object* v_x_1043_){
_start:
{
if (lean_obj_tag(v_x_1041_) == 0)
{
lean_object* v_es_1044_; lean_object* v___x_1045_; size_t v___x_1046_; size_t v___x_1047_; size_t v___x_1048_; lean_object* v_j_1049_; lean_object* v___x_1050_; 
v_es_1044_ = lean_ctor_get(v_x_1041_, 0);
lean_inc_ref(v_es_1044_);
lean_dec_ref(v_x_1041_);
v___x_1045_ = lean_box(2);
v___x_1046_ = ((size_t)5ULL);
v___x_1047_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1);
v___x_1048_ = lean_usize_land(v_x_1042_, v___x_1047_);
v_j_1049_ = lean_usize_to_nat(v___x_1048_);
v___x_1050_ = lean_array_get(v___x_1045_, v_es_1044_, v_j_1049_);
lean_dec(v_j_1049_);
lean_dec_ref(v_es_1044_);
switch(lean_obj_tag(v___x_1050_))
{
case 0:
{
lean_object* v_key_1051_; uint8_t v___x_1052_; 
v_key_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_key_1051_);
lean_dec_ref(v___x_1050_);
v___x_1052_ = lean_name_eq(v_x_1043_, v_key_1051_);
lean_dec(v_key_1051_);
return v___x_1052_;
}
case 1:
{
lean_object* v_node_1053_; size_t v___x_1054_; 
v_node_1053_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_node_1053_);
lean_dec_ref(v___x_1050_);
v___x_1054_ = lean_usize_shift_right(v_x_1042_, v___x_1046_);
v_x_1041_ = v_node_1053_;
v_x_1042_ = v___x_1054_;
goto _start;
}
default: 
{
uint8_t v___x_1056_; 
v___x_1056_ = 0;
return v___x_1056_;
}
}
}
else
{
lean_object* v_ks_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v_ks_1057_ = lean_ctor_get(v_x_1041_, 0);
lean_inc_ref(v_ks_1057_);
lean_dec_ref(v_x_1041_);
v___x_1058_ = lean_unsigned_to_nat(0u);
v___x_1059_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_ks_1057_, v___x_1058_, v_x_1043_);
lean_dec_ref(v_ks_1057_);
return v___x_1059_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___boxed(lean_object* v_x_1060_, lean_object* v_x_1061_, lean_object* v_x_1062_){
_start:
{
size_t v_x_4193__boxed_1063_; uint8_t v_res_1064_; lean_object* v_r_1065_; 
v_x_4193__boxed_1063_ = lean_unbox_usize(v_x_1061_);
lean_dec(v_x_1061_);
v_res_1064_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1060_, v_x_4193__boxed_1063_, v_x_1062_);
lean_dec(v_x_1062_);
v_r_1065_ = lean_box(v_res_1064_);
return v_r_1065_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1066_; uint64_t v___x_1067_; 
v___x_1066_ = lean_unsigned_to_nat(1723u);
v___x_1067_ = lean_uint64_of_nat(v___x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(lean_object* v_x_1068_, lean_object* v_x_1069_){
_start:
{
uint64_t v___y_1071_; 
if (lean_obj_tag(v_x_1069_) == 0)
{
uint64_t v___x_1074_; 
v___x_1074_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0);
v___y_1071_ = v___x_1074_;
goto v___jp_1070_;
}
else
{
uint64_t v_hash_1075_; 
v_hash_1075_ = lean_ctor_get_uint64(v_x_1069_, sizeof(void*)*2);
v___y_1071_ = v_hash_1075_;
goto v___jp_1070_;
}
v___jp_1070_:
{
size_t v___x_1072_; uint8_t v___x_1073_; 
v___x_1072_ = lean_uint64_to_usize(v___y_1071_);
v___x_1073_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1068_, v___x_1072_, v_x_1069_);
return v___x_1073_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___boxed(lean_object* v_x_1076_, lean_object* v_x_1077_){
_start:
{
uint8_t v_res_1078_; lean_object* v_r_1079_; 
v_res_1078_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_1076_, v_x_1077_);
lean_dec(v_x_1077_);
v_r_1079_ = lean_box(v_res_1078_);
return v_r_1079_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(lean_object* v_tactics_1080_, lean_object* v_a_1081_, uint8_t v___x_1082_, lean_object* v_x_1083_, lean_object* v_____s_1084_){
_start:
{
lean_object* v_fst_1085_; lean_object* v_kinds_1086_; uint8_t v___x_1087_; 
v_fst_1085_ = lean_ctor_get(v_x_1083_, 0);
lean_inc(v_fst_1085_);
lean_dec_ref(v_x_1083_);
v_kinds_1086_ = lean_ctor_get(v_tactics_1080_, 1);
lean_inc_ref(v_kinds_1086_);
lean_dec_ref(v_tactics_1080_);
v___x_1087_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_kinds_1086_, v_fst_1085_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; 
lean_dec(v_fst_1085_);
lean_dec(v_a_1081_);
v___x_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1088_, 0, v_____s_1084_);
return v___x_1088_;
}
else
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1089_ = l_Lean_Name_toString(v_a_1081_, v___x_1082_);
v___x_1090_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_1089_, v_fst_1085_, v_____s_1084_);
v___x_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
return v___x_1091_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed(lean_object* v_tactics_1092_, lean_object* v_a_1093_, lean_object* v___x_1094_, lean_object* v_x_1095_, lean_object* v_____s_1096_){
_start:
{
uint8_t v___x_4261__boxed_1097_; lean_object* v_res_1098_; 
v___x_4261__boxed_1097_ = lean_unbox(v___x_1094_);
v_res_1098_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(v_tactics_1092_, v_a_1093_, v___x_4261__boxed_1097_, v_x_1095_, v_____s_1096_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(lean_object* v_f_1099_, lean_object* v_keys_1100_, lean_object* v_vals_1101_, lean_object* v_i_1102_, lean_object* v_acc_1103_){
_start:
{
lean_object* v___x_1104_; uint8_t v___x_1105_; 
v___x_1104_ = lean_array_get_size(v_keys_1100_);
v___x_1105_ = lean_nat_dec_lt(v_i_1102_, v___x_1104_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; 
lean_dec(v_i_1102_);
lean_dec_ref(v_f_1099_);
v___x_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1106_, 0, v_acc_1103_);
return v___x_1106_;
}
else
{
lean_object* v_k_1107_; lean_object* v_v_1108_; lean_object* v___x_1109_; 
v_k_1107_ = lean_array_fget_borrowed(v_keys_1100_, v_i_1102_);
v_v_1108_ = lean_array_fget_borrowed(v_vals_1101_, v_i_1102_);
lean_inc_ref(v_f_1099_);
lean_inc(v_v_1108_);
lean_inc(v_k_1107_);
v___x_1109_ = lean_apply_3(v_f_1099_, v_acc_1103_, v_k_1107_, v_v_1108_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_dec(v_i_1102_);
lean_dec_ref(v_f_1099_);
return v___x_1109_;
}
else
{
lean_object* v_a_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1110_);
lean_dec_ref(v___x_1109_);
v___x_1111_ = lean_unsigned_to_nat(1u);
v___x_1112_ = lean_nat_add(v_i_1102_, v___x_1111_);
lean_dec(v_i_1102_);
v_i_1102_ = v___x_1112_;
v_acc_1103_ = v_a_1110_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_f_1114_, lean_object* v_keys_1115_, lean_object* v_vals_1116_, lean_object* v_i_1117_, lean_object* v_acc_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1114_, v_keys_1115_, v_vals_1116_, v_i_1117_, v_acc_1118_);
lean_dec_ref(v_vals_1116_);
lean_dec_ref(v_keys_1115_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(lean_object* v_f_1120_, lean_object* v_x_1121_, lean_object* v_x_1122_){
_start:
{
if (lean_obj_tag(v_x_1121_) == 0)
{
lean_object* v_es_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1143_; 
v_es_1123_ = lean_ctor_get(v_x_1121_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v_x_1121_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1125_ = v_x_1121_;
v_isShared_1126_ = v_isSharedCheck_1143_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_es_1123_);
lean_dec(v_x_1121_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1143_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1127_ = lean_unsigned_to_nat(0u);
v___x_1128_ = lean_array_get_size(v_es_1123_);
v___x_1129_ = lean_nat_dec_lt(v___x_1127_, v___x_1128_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1131_; 
lean_dec_ref(v_es_1123_);
lean_dec_ref(v_f_1120_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set_tag(v___x_1125_, 1);
lean_ctor_set(v___x_1125_, 0, v_x_1122_);
v___x_1131_ = v___x_1125_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_x_1122_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
else
{
uint8_t v___x_1133_; 
v___x_1133_ = lean_nat_dec_le(v___x_1128_, v___x_1128_);
if (v___x_1133_ == 0)
{
if (v___x_1129_ == 0)
{
lean_object* v___x_1135_; 
lean_dec_ref(v_es_1123_);
lean_dec_ref(v_f_1120_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set_tag(v___x_1125_, 1);
lean_ctor_set(v___x_1125_, 0, v_x_1122_);
v___x_1135_ = v___x_1125_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_x_1122_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
else
{
size_t v___x_1137_; size_t v___x_1138_; lean_object* v___x_1139_; 
lean_del_object(v___x_1125_);
v___x_1137_ = ((size_t)0ULL);
v___x_1138_ = lean_usize_of_nat(v___x_1128_);
v___x_1139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1120_, v_es_1123_, v___x_1137_, v___x_1138_, v_x_1122_);
lean_dec_ref(v_es_1123_);
return v___x_1139_;
}
}
else
{
size_t v___x_1140_; size_t v___x_1141_; lean_object* v___x_1142_; 
lean_del_object(v___x_1125_);
v___x_1140_ = ((size_t)0ULL);
v___x_1141_ = lean_usize_of_nat(v___x_1128_);
v___x_1142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1120_, v_es_1123_, v___x_1140_, v___x_1141_, v_x_1122_);
lean_dec_ref(v_es_1123_);
return v___x_1142_;
}
}
}
}
else
{
lean_object* v_ks_1144_; lean_object* v_vs_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v_ks_1144_ = lean_ctor_get(v_x_1121_, 0);
lean_inc_ref(v_ks_1144_);
v_vs_1145_ = lean_ctor_get(v_x_1121_, 1);
lean_inc_ref(v_vs_1145_);
lean_dec_ref(v_x_1121_);
v___x_1146_ = lean_unsigned_to_nat(0u);
v___x_1147_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1120_, v_ks_1144_, v_vs_1145_, v___x_1146_, v_x_1122_);
lean_dec_ref(v_vs_1145_);
lean_dec_ref(v_ks_1144_);
return v___x_1147_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(lean_object* v_f_1148_, lean_object* v_as_1149_, size_t v_i_1150_, size_t v_stop_1151_, lean_object* v_b_1152_){
_start:
{
lean_object* v_a_1154_; lean_object* v___y_1159_; uint8_t v___x_1161_; 
v___x_1161_ = lean_usize_dec_eq(v_i_1150_, v_stop_1151_);
if (v___x_1161_ == 0)
{
lean_object* v___x_1162_; 
v___x_1162_ = lean_array_uget_borrowed(v_as_1149_, v_i_1150_);
switch(lean_obj_tag(v___x_1162_))
{
case 0:
{
lean_object* v_key_1163_; lean_object* v_val_1164_; lean_object* v___x_1165_; 
v_key_1163_ = lean_ctor_get(v___x_1162_, 0);
v_val_1164_ = lean_ctor_get(v___x_1162_, 1);
lean_inc_ref(v_f_1148_);
lean_inc(v_val_1164_);
lean_inc(v_key_1163_);
v___x_1165_ = lean_apply_3(v_f_1148_, v_b_1152_, v_key_1163_, v_val_1164_);
v___y_1159_ = v___x_1165_;
goto v___jp_1158_;
}
case 1:
{
lean_object* v_node_1166_; lean_object* v___x_1167_; 
v_node_1166_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_node_1166_);
lean_inc_ref(v_f_1148_);
v___x_1167_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1148_, v_node_1166_, v_b_1152_);
v___y_1159_ = v___x_1167_;
goto v___jp_1158_;
}
default: 
{
v_a_1154_ = v_b_1152_;
goto v___jp_1153_;
}
}
}
else
{
lean_object* v___x_1168_; 
lean_dec_ref(v_f_1148_);
v___x_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1168_, 0, v_b_1152_);
return v___x_1168_;
}
v___jp_1153_:
{
size_t v___x_1155_; size_t v___x_1156_; 
v___x_1155_ = ((size_t)1ULL);
v___x_1156_ = lean_usize_add(v_i_1150_, v___x_1155_);
v_i_1150_ = v___x_1156_;
v_b_1152_ = v_a_1154_;
goto _start;
}
v___jp_1158_:
{
if (lean_obj_tag(v___y_1159_) == 0)
{
lean_dec_ref(v_f_1148_);
return v___y_1159_;
}
else
{
lean_object* v_a_1160_; 
v_a_1160_ = lean_ctor_get(v___y_1159_, 0);
lean_inc(v_a_1160_);
lean_dec_ref(v___y_1159_);
v_a_1154_ = v_a_1160_;
goto v___jp_1153_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_f_1169_, lean_object* v_as_1170_, lean_object* v_i_1171_, lean_object* v_stop_1172_, lean_object* v_b_1173_){
_start:
{
size_t v_i_boxed_1174_; size_t v_stop_boxed_1175_; lean_object* v_res_1176_; 
v_i_boxed_1174_ = lean_unbox_usize(v_i_1171_);
lean_dec(v_i_1171_);
v_stop_boxed_1175_ = lean_unbox_usize(v_stop_1172_);
lean_dec(v_stop_1172_);
v_res_1176_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1169_, v_as_1170_, v_i_boxed_1174_, v_stop_boxed_1175_, v_b_1173_);
lean_dec_ref(v_as_1170_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0(lean_object* v_f_1177_, lean_object* v_s_1178_, lean_object* v_a_1179_, lean_object* v_b_1180_){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1181_, 0, v_a_1179_);
lean_ctor_set(v___x_1181_, 1, v_b_1180_);
v___x_1182_ = lean_apply_2(v_f_1177_, v___x_1181_, v_s_1178_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1182_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1182_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
v_a_1191_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1182_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1182_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(lean_object* v_map_1199_, lean_object* v_init_1200_, lean_object* v_f_1201_){
_start:
{
lean_object* v___f_1202_; lean_object* v___x_1203_; lean_object* v_a_1204_; 
v___f_1202_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1202_, 0, v_f_1201_);
v___x_1203_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v___f_1202_, v_map_1199_, v_init_1200_);
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_a_1204_);
lean_dec_ref(v___x_1203_);
return v_a_1204_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1205_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1206_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0);
v___x_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1206_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(lean_object* v_tactics_1208_, lean_object* v_a_1209_, uint8_t v___x_1210_, lean_object* v_as_x27_1211_, lean_object* v_b_1212_){
_start:
{
if (lean_obj_tag(v_as_x27_1211_) == 0)
{
lean_dec(v_a_1209_);
lean_dec_ref(v_tactics_1208_);
return v_b_1212_;
}
else
{
lean_object* v_head_1213_; lean_object* v_fst_1214_; lean_object* v_info_1215_; lean_object* v_tail_1216_; lean_object* v_collectKinds_1217_; lean_object* v___x_1218_; lean_object* v___f_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v_head_1213_ = lean_ctor_get(v_as_x27_1211_, 0);
v_fst_1214_ = lean_ctor_get(v_head_1213_, 0);
v_info_1215_ = lean_ctor_get(v_fst_1214_, 0);
lean_inc_ref(v_info_1215_);
v_tail_1216_ = lean_ctor_get(v_as_x27_1211_, 1);
lean_inc(v_tail_1216_);
lean_dec_ref(v_as_x27_1211_);
v_collectKinds_1217_ = lean_ctor_get(v_info_1215_, 1);
lean_inc_ref(v_collectKinds_1217_);
lean_dec_ref(v_info_1215_);
v___x_1218_ = lean_box(v___x_1210_);
lean_inc(v_a_1209_);
lean_inc_ref(v_tactics_1208_);
v___f_1219_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1219_, 0, v_tactics_1208_);
lean_closure_set(v___f_1219_, 1, v_a_1209_);
lean_closure_set(v___f_1219_, 2, v___x_1218_);
v___x_1220_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1);
v___x_1221_ = lean_apply_1(v_collectKinds_1217_, v___x_1220_);
v___x_1222_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v___x_1221_, v_b_1212_, v___f_1219_);
v_as_x27_1211_ = v_tail_1216_;
v_b_1212_ = v___x_1222_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___boxed(lean_object* v_tactics_1224_, lean_object* v_a_1225_, lean_object* v___x_1226_, lean_object* v_as_x27_1227_, lean_object* v_b_1228_){
_start:
{
uint8_t v___x_4435__boxed_1229_; lean_object* v_res_1230_; 
v___x_4435__boxed_1229_ = lean_unbox(v___x_1226_);
v_res_1230_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1224_, v_a_1225_, v___x_4435__boxed_1229_, v_as_x27_1227_, v_b_1228_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(lean_object* v_tactics_1234_, lean_object* v_init_1235_, lean_object* v_x_1236_){
_start:
{
if (lean_obj_tag(v_x_1236_) == 0)
{
lean_object* v_k_1237_; lean_object* v_v_1238_; lean_object* v_l_1239_; lean_object* v_r_1240_; lean_object* v___x_1241_; lean_object* v_a_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
v_k_1237_ = lean_ctor_get(v_x_1236_, 1);
lean_inc(v_k_1237_);
v_v_1238_ = lean_ctor_get(v_x_1236_, 2);
lean_inc(v_v_1238_);
v_l_1239_ = lean_ctor_get(v_x_1236_, 3);
lean_inc(v_l_1239_);
v_r_1240_ = lean_ctor_get(v_x_1236_, 4);
lean_inc(v_r_1240_);
lean_dec_ref(v_x_1236_);
lean_inc_ref(v_tactics_1234_);
v___x_1241_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_1234_, v_init_1235_, v_l_1239_);
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1242_);
v___x_1243_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__1));
v___x_1244_ = lean_name_eq(v_k_1237_, v___x_1243_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; 
lean_dec_ref(v___x_1241_);
lean_inc_ref(v_tactics_1234_);
v___x_1245_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1234_, v_k_1237_, v___x_1244_, v_v_1238_, v_a_1242_);
v_init_1235_ = v___x_1245_;
v_x_1236_ = v_r_1240_;
goto _start;
}
else
{
lean_object* v_a_1247_; 
lean_dec(v_a_1242_);
lean_dec(v_v_1238_);
lean_dec(v_k_1237_);
v_a_1247_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1247_);
lean_dec_ref(v___x_1241_);
v_init_1235_ = v_a_1247_;
v_x_1236_ = v_r_1240_;
goto _start;
}
}
else
{
lean_object* v___x_1249_; 
lean_dec_ref(v_tactics_1234_);
v___x_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1249_, 0, v_init_1235_);
return v___x_1249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(lean_object* v_tactics_1250_, lean_object* v_table_1251_, lean_object* v_firsts_1252_){
_start:
{
lean_object* v___x_1253_; lean_object* v_a_1254_; 
v___x_1253_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_1250_, v_firsts_1252_, v_table_1251_);
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1254_);
lean_dec_ref(v___x_1253_);
return v_a_1254_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(lean_object* v_00_u03b2_1255_, lean_object* v_x_1256_, lean_object* v_x_1257_){
_start:
{
uint8_t v___x_1258_; 
v___x_1258_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_1256_, v_x_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___boxed(lean_object* v_00_u03b2_1259_, lean_object* v_x_1260_, lean_object* v_x_1261_){
_start:
{
uint8_t v_res_1262_; lean_object* v_r_1263_; 
v_res_1262_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(v_00_u03b2_1259_, v_x_1260_, v_x_1261_);
lean_dec(v_x_1261_);
v_r_1263_ = lean_box(v_res_1262_);
return v_r_1263_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1(lean_object* v___x_1264_, lean_object* v_k_1265_, lean_object* v_t_1266_, lean_object* v_hl_1267_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_1264_, v_k_1265_, v_t_1266_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(lean_object* v_00_u03c3_1269_, lean_object* v_00_u03b2_1270_, lean_object* v_map_1271_, lean_object* v_init_1272_, lean_object* v_f_1273_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_1271_, v_init_1272_, v_f_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(lean_object* v_tactics_1275_, lean_object* v_a_1276_, uint8_t v___x_1277_, lean_object* v_as_1278_, lean_object* v_as_x27_1279_, lean_object* v_b_1280_, lean_object* v_a_1281_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1275_, v_a_1276_, v___x_1277_, v_as_x27_1279_, v_b_1280_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___boxed(lean_object* v_tactics_1283_, lean_object* v_a_1284_, lean_object* v___x_1285_, lean_object* v_as_1286_, lean_object* v_as_x27_1287_, lean_object* v_b_1288_, lean_object* v_a_1289_){
_start:
{
uint8_t v___x_4518__boxed_1290_; lean_object* v_res_1291_; 
v___x_4518__boxed_1290_ = lean_unbox(v___x_1285_);
v_res_1291_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(v_tactics_1283_, v_a_1284_, v___x_4518__boxed_1290_, v_as_1286_, v_as_x27_1287_, v_b_1288_, v_a_1289_);
lean_dec(v_as_1286_);
return v_res_1291_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(lean_object* v_00_u03b2_1292_, lean_object* v_x_1293_, size_t v_x_1294_, lean_object* v_x_1295_){
_start:
{
uint8_t v___x_1296_; 
v___x_1296_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1293_, v_x_1294_, v_x_1295_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1297_, lean_object* v_x_1298_, lean_object* v_x_1299_, lean_object* v_x_1300_){
_start:
{
size_t v_x_4527__boxed_1301_; uint8_t v_res_1302_; lean_object* v_r_1303_; 
v_x_4527__boxed_1301_ = lean_unbox_usize(v_x_1299_);
lean_dec(v_x_1299_);
v_res_1302_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(v_00_u03b2_1297_, v_x_1298_, v_x_4527__boxed_1301_, v_x_1300_);
lean_dec(v_x_1300_);
v_r_1303_ = lean_box(v_res_1302_);
return v_r_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3___redArg(lean_object* v_map_1304_, lean_object* v_f_1305_, lean_object* v_init_1306_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1305_, v_map_1304_, v_init_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3(lean_object* v_00_u03c3_1308_, lean_object* v_00_u03c3_1309_, lean_object* v_00_u03b2_1310_, lean_object* v_map_1311_, lean_object* v_f_1312_, lean_object* v_init_1313_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1312_, v_map_1311_, v_init_1313_);
return v___x_1314_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1315_, lean_object* v_keys_1316_, lean_object* v_vals_1317_, lean_object* v_heq_1318_, lean_object* v_i_1319_, lean_object* v_k_1320_){
_start:
{
uint8_t v___x_1321_; 
v___x_1321_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_1316_, v_i_1319_, v_k_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1322_, lean_object* v_keys_1323_, lean_object* v_vals_1324_, lean_object* v_heq_1325_, lean_object* v_i_1326_, lean_object* v_k_1327_){
_start:
{
uint8_t v_res_1328_; lean_object* v_r_1329_; 
v_res_1328_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(v_00_u03b2_1322_, v_keys_1323_, v_vals_1324_, v_heq_1325_, v_i_1326_, v_k_1327_);
lean_dec(v_k_1327_);
lean_dec_ref(v_vals_1324_);
lean_dec_ref(v_keys_1323_);
v_r_1329_ = lean_box(v_res_1328_);
return v_r_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5(lean_object* v_00_u03c3_1330_, lean_object* v_00_u03c3_1331_, lean_object* v_00_u03b1_1332_, lean_object* v_00_u03b2_1333_, lean_object* v_f_1334_, lean_object* v_x_1335_, lean_object* v_x_1336_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1334_, v_x_1335_, v_x_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(lean_object* v_00_u03b1_1338_, lean_object* v_00_u03b2_1339_, lean_object* v_00_u03c3_1340_, lean_object* v_00_u03c3_1341_, lean_object* v_f_1342_, lean_object* v_as_1343_, size_t v_i_1344_, size_t v_stop_1345_, lean_object* v_b_1346_){
_start:
{
lean_object* v___x_1347_; 
v___x_1347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1342_, v_as_1343_, v_i_1344_, v_stop_1345_, v_b_1346_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1348_, lean_object* v_00_u03b2_1349_, lean_object* v_00_u03c3_1350_, lean_object* v_00_u03c3_1351_, lean_object* v_f_1352_, lean_object* v_as_1353_, lean_object* v_i_1354_, lean_object* v_stop_1355_, lean_object* v_b_1356_){
_start:
{
size_t v_i_boxed_1357_; size_t v_stop_boxed_1358_; lean_object* v_res_1359_; 
v_i_boxed_1357_ = lean_unbox_usize(v_i_1354_);
lean_dec(v_i_1354_);
v_stop_boxed_1358_ = lean_unbox_usize(v_stop_1355_);
lean_dec(v_stop_1355_);
v_res_1359_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(v_00_u03b1_1348_, v_00_u03b2_1349_, v_00_u03c3_1350_, v_00_u03c3_1351_, v_f_1352_, v_as_1353_, v_i_boxed_1357_, v_stop_boxed_1358_, v_b_1356_);
lean_dec_ref(v_as_1353_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(lean_object* v_00_u03c3_1360_, lean_object* v_00_u03c3_1361_, lean_object* v_00_u03b1_1362_, lean_object* v_00_u03b2_1363_, lean_object* v_f_1364_, lean_object* v_keys_1365_, lean_object* v_vals_1366_, lean_object* v_heq_1367_, lean_object* v_i_1368_, lean_object* v_acc_1369_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1364_, v_keys_1365_, v_vals_1366_, v_i_1368_, v_acc_1369_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03c3_1371_, lean_object* v_00_u03c3_1372_, lean_object* v_00_u03b1_1373_, lean_object* v_00_u03b2_1374_, lean_object* v_f_1375_, lean_object* v_keys_1376_, lean_object* v_vals_1377_, lean_object* v_heq_1378_, lean_object* v_i_1379_, lean_object* v_acc_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(v_00_u03c3_1371_, v_00_u03c3_1372_, v_00_u03b1_1373_, v_00_u03b2_1374_, v_f_1375_, v_keys_1376_, v_vals_1377_, v_heq_1378_, v_i_1379_, v_acc_1380_);
lean_dec_ref(v_vals_1377_);
lean_dec_ref(v_keys_1376_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0(lean_object* v_x1_1382_, lean_object* v_x2_1383_){
_start:
{
lean_object* v_fst_1384_; lean_object* v_snd_1385_; lean_object* v___x_1386_; 
v_fst_1384_ = lean_ctor_get(v_x2_1383_, 0);
lean_inc(v_fst_1384_);
v_snd_1385_ = lean_ctor_get(v_x2_1383_, 1);
lean_inc(v_snd_1385_);
lean_dec_ref(v_x2_1383_);
v___x_1386_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_1384_, v_snd_1385_, v_x1_1382_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1(lean_object* v___f_1406_, lean_object* v_x1_1407_, lean_object* v_x2_1408_){
_start:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
v___x_1409_ = lean_unsigned_to_nat(0u);
v___x_1410_ = lean_array_get_size(v_x2_1408_);
v___x_1411_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_1412_ = lean_nat_dec_lt(v___x_1409_, v___x_1410_);
if (v___x_1412_ == 0)
{
lean_dec_ref(v_x2_1408_);
lean_dec_ref(v___f_1406_);
return v_x1_1407_;
}
else
{
uint8_t v___x_1413_; 
v___x_1413_ = lean_nat_dec_le(v___x_1410_, v___x_1410_);
if (v___x_1413_ == 0)
{
if (v___x_1412_ == 0)
{
lean_dec_ref(v_x2_1408_);
lean_dec_ref(v___f_1406_);
return v_x1_1407_;
}
else
{
size_t v___x_1414_; size_t v___x_1415_; lean_object* v___x_1416_; 
v___x_1414_ = ((size_t)0ULL);
v___x_1415_ = lean_usize_of_nat(v___x_1410_);
v___x_1416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1411_, v___f_1406_, v_x2_1408_, v___x_1414_, v___x_1415_, v_x1_1407_);
return v___x_1416_;
}
}
else
{
size_t v___x_1417_; size_t v___x_1418_; lean_object* v___x_1419_; 
v___x_1417_ = ((size_t)0ULL);
v___x_1418_ = lean_usize_of_nat(v___x_1410_);
v___x_1419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1411_, v___f_1406_, v_x2_1408_, v___x_1417_, v___x_1418_, v_x1_1407_);
return v___x_1419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(lean_object* v___x_1423_, lean_object* v___x_1424_, lean_object* v___x_1425_, lean_object* v___x_1426_, lean_object* v_toPure_1427_, lean_object* v___x_1428_, lean_object* v___f_1429_, lean_object* v_env_1430_){
_start:
{
lean_object* v___x_1431_; lean_object* v_ext_1432_; lean_object* v_toEnvExtension_1433_; lean_object* v_asyncMode_1434_; lean_object* v___x_1435_; lean_object* v_categories_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1431_ = l_Lean_Parser_parserExtension;
v_ext_1432_ = lean_ctor_get(v___x_1431_, 1);
lean_inc_ref(v_ext_1432_);
v_toEnvExtension_1433_ = lean_ctor_get(v_ext_1432_, 0);
lean_inc_ref(v_toEnvExtension_1433_);
lean_dec_ref(v_ext_1432_);
v_asyncMode_1434_ = lean_ctor_get(v_toEnvExtension_1433_, 2);
lean_inc(v_asyncMode_1434_);
lean_dec_ref(v_toEnvExtension_1433_);
lean_inc_ref(v_env_1430_);
v___x_1435_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1423_, v___x_1431_, v_env_1430_, v_asyncMode_1434_);
lean_dec(v_asyncMode_1434_);
v_categories_1436_ = lean_ctor_get(v___x_1435_, 2);
lean_inc_ref(v_categories_1436_);
lean_dec(v___x_1435_);
v___x_1437_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_1438_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_1424_, v___x_1425_, v_categories_1436_, v___x_1437_);
if (lean_obj_tag(v___x_1438_) == 1)
{
lean_object* v_val_1439_; lean_object* v___y_1441_; lean_object* v___x_1448_; lean_object* v_toEnvExtension_1449_; lean_object* v_exportEntriesFn_1450_; lean_object* v_asyncMode_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v_importedEntries_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; uint8_t v___x_1464_; 
v_val_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_val_1439_);
lean_dec_ref(v___x_1438_);
v___x_1448_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc_ref(v_toEnvExtension_1449_);
v_exportEntriesFn_1450_ = lean_ctor_get(v___x_1448_, 4);
lean_inc_ref(v_exportEntriesFn_1450_);
v_asyncMode_1451_ = lean_ctor_get(v_toEnvExtension_1449_, 2);
lean_inc(v_asyncMode_1451_);
v___x_1452_ = lean_box(0);
lean_inc_ref(v_env_1430_);
v___x_1453_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1426_, v_toEnvExtension_1449_, v_env_1430_, v_asyncMode_1451_, v___x_1452_);
lean_dec_ref(v_toEnvExtension_1449_);
v_importedEntries_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc_ref(v_importedEntries_1454_);
lean_dec(v___x_1453_);
v___x_1455_ = lean_box(1);
lean_inc_ref(v_env_1430_);
v___x_1456_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1428_, v___x_1448_, v_env_1430_, v_asyncMode_1451_, v___x_1452_);
lean_dec(v_asyncMode_1451_);
v___x_1457_ = 0;
v___x_1458_ = lean_box(v___x_1457_);
v___x_1459_ = lean_apply_3(v_exportEntriesFn_1450_, v_env_1430_, v___x_1456_, v___x_1458_);
v___x_1460_ = lean_array_push(v_importedEntries_1454_, v___x_1459_);
v___x_1461_ = lean_unsigned_to_nat(0u);
v___x_1462_ = lean_array_get_size(v___x_1460_);
v___x_1463_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_1464_ = lean_nat_dec_lt(v___x_1461_, v___x_1462_);
if (v___x_1464_ == 0)
{
lean_dec_ref(v___x_1460_);
lean_dec_ref(v___f_1429_);
v___y_1441_ = v___x_1455_;
goto v___jp_1440_;
}
else
{
uint8_t v___x_1465_; 
v___x_1465_ = lean_nat_dec_le(v___x_1462_, v___x_1462_);
if (v___x_1465_ == 0)
{
if (v___x_1464_ == 0)
{
lean_dec_ref(v___x_1460_);
lean_dec_ref(v___f_1429_);
v___y_1441_ = v___x_1455_;
goto v___jp_1440_;
}
else
{
size_t v___x_1466_; size_t v___x_1467_; lean_object* v___x_1468_; 
v___x_1466_ = ((size_t)0ULL);
v___x_1467_ = lean_usize_of_nat(v___x_1462_);
v___x_1468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1463_, v___f_1429_, v___x_1460_, v___x_1466_, v___x_1467_, v___x_1455_);
v___y_1441_ = v___x_1468_;
goto v___jp_1440_;
}
}
else
{
size_t v___x_1469_; size_t v___x_1470_; lean_object* v___x_1471_; 
v___x_1469_ = ((size_t)0ULL);
v___x_1470_ = lean_usize_of_nat(v___x_1462_);
v___x_1471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1463_, v___f_1429_, v___x_1460_, v___x_1469_, v___x_1470_, v___x_1455_);
v___y_1441_ = v___x_1471_;
goto v___jp_1440_;
}
}
v___jp_1440_:
{
lean_object* v_tables_1442_; lean_object* v_leadingTable_1443_; lean_object* v_trailingTable_1444_; lean_object* v_firstTokens_1445_; lean_object* v_firstTokens_1446_; lean_object* v___x_1447_; 
v_tables_1442_ = lean_ctor_get(v_val_1439_, 2);
v_leadingTable_1443_ = lean_ctor_get(v_tables_1442_, 0);
v_trailingTable_1444_ = lean_ctor_get(v_tables_1442_, 2);
lean_inc(v_trailingTable_1444_);
lean_inc(v_leadingTable_1443_);
lean_inc(v_val_1439_);
v_firstTokens_1445_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_1439_, v_leadingTable_1443_, v___y_1441_);
v_firstTokens_1446_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_1439_, v_trailingTable_1444_, v_firstTokens_1445_);
v___x_1447_ = lean_apply_2(v_toPure_1427_, lean_box(0), v_firstTokens_1446_);
return v___x_1447_;
}
}
else
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_dec(v___x_1438_);
lean_dec_ref(v_env_1430_);
lean_dec_ref(v___f_1429_);
lean_dec(v___x_1428_);
lean_dec_ref(v___x_1426_);
v___x_1472_ = lean_box(1);
v___x_1473_ = lean_apply_2(v_toPure_1427_, lean_box(0), v___x_1472_);
return v___x_1473_;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2(void){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = lean_box(1);
v___x_1478_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(lean_object* v_inst_1481_, lean_object* v_inst_1482_){
_start:
{
lean_object* v_toApplicative_1483_; lean_object* v_toBind_1484_; lean_object* v_getEnv_1485_; lean_object* v_toPure_1486_; lean_object* v___f_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___f_1493_; lean_object* v___x_1494_; 
v_toApplicative_1483_ = lean_ctor_get(v_inst_1481_, 0);
lean_inc_ref(v_toApplicative_1483_);
v_toBind_1484_ = lean_ctor_get(v_inst_1481_, 1);
lean_inc(v_toBind_1484_);
lean_dec_ref(v_inst_1481_);
v_getEnv_1485_ = lean_ctor_get(v_inst_1482_, 0);
lean_inc(v_getEnv_1485_);
lean_dec_ref(v_inst_1482_);
v_toPure_1486_ = lean_ctor_get(v_toApplicative_1483_, 1);
lean_inc(v_toPure_1486_);
lean_dec_ref(v_toApplicative_1483_);
v___f_1487_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1));
v___x_1488_ = lean_box(1);
v___x_1489_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_1490_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_1491_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___x_1492_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___f_1493_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2), 8, 7);
lean_closure_set(v___f_1493_, 0, v___x_1492_);
lean_closure_set(v___f_1493_, 1, v___x_1490_);
lean_closure_set(v___f_1493_, 2, v___x_1491_);
lean_closure_set(v___f_1493_, 3, v___x_1489_);
lean_closure_set(v___f_1493_, 4, v_toPure_1486_);
lean_closure_set(v___f_1493_, 5, v___x_1488_);
lean_closure_set(v___f_1493_, 6, v___f_1487_);
v___x_1494_ = lean_apply_4(v_toBind_1484_, lean_box(0), lean_box(0), v_getEnv_1485_, v___f_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens(lean_object* v_m_1495_, lean_object* v_inst_1496_, lean_object* v_inst_1497_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(v_inst_1496_, v_inst_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(lean_object* v_x_1499_, lean_object* v_y_1500_){
_start:
{
uint8_t v___x_1501_; 
v___x_1501_ = lean_nat_dec_lt(v_x_1499_, v_y_1500_);
if (v___x_1501_ == 0)
{
uint8_t v___x_1502_; 
v___x_1502_ = lean_nat_dec_eq(v_x_1499_, v_y_1500_);
if (v___x_1502_ == 0)
{
uint8_t v___x_1503_; 
v___x_1503_ = 2;
return v___x_1503_;
}
else
{
uint8_t v___x_1504_; 
v___x_1504_ = 1;
return v___x_1504_;
}
}
else
{
uint8_t v___x_1505_; 
v___x_1505_ = 0;
return v___x_1505_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___boxed(lean_object* v_x_1506_, lean_object* v_y_1507_){
_start:
{
uint8_t v_res_1508_; lean_object* v_r_1509_; 
v_res_1508_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(v_x_1506_, v_y_1507_);
lean_dec(v_y_1507_);
lean_dec(v_x_1506_);
v_r_1509_ = lean_box(v_res_1508_);
return v_r_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1(lean_object* v___f_1510_, lean_object* v_a_1511_, lean_object* v_x_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_fst_1514_; lean_object* v_snd_1515_; lean_object* v_r_1516_; lean_object* v___x_1517_; 
v_fst_1514_ = lean_ctor_get(v_a_1511_, 0);
lean_inc(v_fst_1514_);
v_snd_1515_ = lean_ctor_get(v_a_1511_, 1);
lean_inc(v_snd_1515_);
lean_dec_ref(v_a_1511_);
v_r_1516_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_1510_, v_fst_1514_, v_snd_1515_, v___y_1513_);
v___x_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1517_, 0, v_r_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2(lean_object* v_n_1524_, lean_object* v___y_1525_, lean_object* v___f_1526_, lean_object* v_toPure_1527_, lean_object* v_firsts_1528_, lean_object* v_____do__lift_1529_){
_start:
{
lean_object* v___y_1531_; lean_object* v_val_1563_; 
if (lean_obj_tag(v_____do__lift_1529_) == 0)
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__3));
lean_inc(v_n_1524_);
v___x_1566_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___x_1565_, v_firsts_1528_, v_n_1524_);
if (lean_obj_tag(v___x_1566_) == 0)
{
uint8_t v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1567_ = 1;
lean_inc(v_n_1524_);
v___x_1568_ = l_Lean_Name_toString(v_n_1524_, v___x_1567_);
v___x_1569_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1568_);
v___y_1531_ = v___x_1569_;
goto v___jp_1530_;
}
else
{
lean_object* v_val_1570_; 
v_val_1570_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_val_1570_);
lean_dec_ref(v___x_1566_);
v_val_1563_ = v_val_1570_;
goto v___jp_1562_;
}
}
else
{
lean_object* v_val_1571_; 
lean_dec(v_firsts_1528_);
v_val_1571_ = lean_ctor_get(v_____do__lift_1529_, 0);
lean_inc(v_val_1571_);
lean_dec_ref(v_____do__lift_1529_);
v_val_1563_ = v_val_1571_;
goto v___jp_1562_;
}
v___jp_1530_:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; uint8_t v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v_r_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1532_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__0));
v___x_1533_ = lean_unsigned_to_nat(0u);
v___x_1534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
lean_ctor_set(v___x_1534_, 1, v___y_1531_);
v___x_1535_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1532_);
lean_ctor_set(v___x_1535_, 1, v___x_1534_);
v___x_1536_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1535_);
lean_ctor_set(v___x_1536_, 1, v___x_1532_);
v___x_1537_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__2));
v___x_1538_ = lean_box(2);
v___x_1539_ = 1;
lean_inc(v_n_1524_);
v___x_1540_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1524_, v___x_1539_);
v___x_1541_ = lean_string_utf8_byte_size(v___x_1540_);
v___x_1542_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1540_);
lean_ctor_set(v___x_1542_, 1, v___x_1533_);
lean_ctor_set(v___x_1542_, 2, v___x_1541_);
v___x_1543_ = lean_box(0);
lean_inc(v_n_1524_);
v___x_1544_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1544_, 0, v_n_1524_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
v___x_1545_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1544_);
lean_ctor_set(v___x_1545_, 1, v___x_1543_);
lean_inc(v_n_1524_);
v___x_1546_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1538_);
lean_ctor_set(v___x_1546_, 1, v___x_1542_);
lean_ctor_set(v___x_1546_, 2, v_n_1524_);
lean_ctor_set(v___x_1546_, 3, v___x_1545_);
v___x_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1537_);
lean_ctor_set(v___x_1547_, 1, v___x_1546_);
v___x_1548_ = l_Lean_LocalContext_empty;
v___x_1549_ = lean_box(0);
v___x_1550_ = l_Lean_Expr_const___override(v_n_1524_, v___y_1525_);
v___x_1551_ = 0;
v___x_1552_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1552_, 0, v___x_1547_);
lean_ctor_set(v___x_1552_, 1, v___x_1548_);
lean_ctor_set(v___x_1552_, 2, v___x_1549_);
lean_ctor_set(v___x_1552_, 3, v___x_1550_);
lean_ctor_set_uint8(v___x_1552_, sizeof(void*)*4, v___x_1551_);
lean_ctor_set_uint8(v___x_1552_, sizeof(void*)*4 + 1, v___x_1551_);
v___x_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
v___x_1554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1533_);
lean_ctor_set(v___x_1554_, 1, v___x_1553_);
v___x_1555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
lean_ctor_set(v___x_1555_, 1, v___x_1543_);
v___x_1556_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v_r_1557_ = lean_box(1);
v___x_1558_ = l_List_forIn_x27_loop___redArg(v___x_1556_, v___f_1526_, v___x_1555_, v_r_1557_);
v___x_1559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1536_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
v___x_1561_ = lean_apply_2(v_toPure_1527_, lean_box(0), v___x_1560_);
return v___x_1561_;
}
v___jp_1562_:
{
lean_object* v___x_1564_; 
v___x_1564_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1564_, 0, v_val_1563_);
v___y_1531_ = v___x_1564_;
goto v___jp_1530_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__3(lean_object* v_n_1572_, lean_object* v___f_1573_, lean_object* v_toPure_1574_, lean_object* v_firsts_1575_, lean_object* v_inst_1576_, lean_object* v_inst_1577_, lean_object* v_toBind_1578_, lean_object* v___x_1579_, lean_object* v___x_1580_, lean_object* v___f_1581_, lean_object* v_env_1582_){
_start:
{
lean_object* v___y_1584_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = l_Lean_Environment_constants(v_env_1582_);
lean_inc(v_n_1572_);
v___x_1589_ = l_Lean_SMap_find_x3f_x27___redArg(v___x_1579_, v___x_1580_, v___x_1588_, v_n_1572_);
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v___x_1590_; 
lean_dec_ref(v___f_1581_);
v___x_1590_ = lean_box(0);
v___y_1584_ = v___x_1590_;
goto v___jp_1583_;
}
else
{
lean_object* v_val_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v_val_1591_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_val_1591_);
lean_dec_ref(v___x_1589_);
v___x_1592_ = l_Lean_ConstantInfo_levelParams(v_val_1591_);
lean_dec(v_val_1591_);
v___x_1593_ = lean_box(0);
v___x_1594_ = l_List_mapTR_loop___redArg(v___f_1581_, v___x_1592_, v___x_1593_);
v___y_1584_ = v___x_1594_;
goto v___jp_1583_;
}
v___jp_1583_:
{
lean_object* v___f_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; 
lean_inc(v_n_1572_);
v___f_1585_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2), 6, 5);
lean_closure_set(v___f_1585_, 0, v_n_1572_);
lean_closure_set(v___f_1585_, 1, v___y_1584_);
lean_closure_set(v___f_1585_, 2, v___f_1573_);
lean_closure_set(v___f_1585_, 3, v_toPure_1574_);
lean_closure_set(v___f_1585_, 4, v_firsts_1575_);
v___x_1586_ = l_Lean_Parser_Tactic_Doc_customTacticName___redArg(v_inst_1576_, v_inst_1577_, v_n_1572_);
v___x_1587_ = lean_apply_4(v_toBind_1578_, lean_box(0), lean_box(0), v___x_1586_, v___f_1585_);
return v___x_1587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(lean_object* v_inst_1599_, lean_object* v_inst_1600_, lean_object* v_firsts_1601_, lean_object* v_n_1602_){
_start:
{
lean_object* v_toApplicative_1603_; lean_object* v_toBind_1604_; lean_object* v_getEnv_1605_; lean_object* v_toPure_1606_; lean_object* v___f_1607_; lean_object* v___f_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___f_1611_; lean_object* v___x_1612_; 
v_toApplicative_1603_ = lean_ctor_get(v_inst_1599_, 0);
v_toBind_1604_ = lean_ctor_get(v_inst_1599_, 1);
lean_inc(v_toBind_1604_);
v_getEnv_1605_ = lean_ctor_get(v_inst_1600_, 0);
lean_inc(v_getEnv_1605_);
v_toPure_1606_ = lean_ctor_get(v_toApplicative_1603_, 1);
lean_inc(v_toPure_1606_);
v___f_1607_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__1));
v___f_1608_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__2));
v___x_1609_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_1610_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
lean_inc(v_toBind_1604_);
v___f_1611_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__3), 11, 10);
lean_closure_set(v___f_1611_, 0, v_n_1602_);
lean_closure_set(v___f_1611_, 1, v___f_1607_);
lean_closure_set(v___f_1611_, 2, v_toPure_1606_);
lean_closure_set(v___f_1611_, 3, v_firsts_1601_);
lean_closure_set(v___f_1611_, 4, v_inst_1599_);
lean_closure_set(v___f_1611_, 5, v_inst_1600_);
lean_closure_set(v___f_1611_, 6, v_toBind_1604_);
lean_closure_set(v___f_1611_, 7, v___x_1609_);
lean_closure_set(v___f_1611_, 8, v___x_1610_);
lean_closure_set(v___f_1611_, 9, v___f_1608_);
v___x_1612_ = lean_apply_4(v_toBind_1604_, lean_box(0), lean_box(0), v_getEnv_1605_, v___f_1611_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName(lean_object* v_m_1613_, lean_object* v_inst_1614_, lean_object* v_inst_1615_, lean_object* v_firsts_1616_, lean_object* v_n_1617_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(v_inst_1614_, v_inst_1615_, v_firsts_1616_, v_n_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(lean_object* v_s_1621_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0));
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___boxed(lean_object* v_s_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v_s_1623_);
lean_dec_ref(v_s_1623_);
return v_res_1624_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(uint8_t v___x_1625_, lean_object* v_x1_1626_, lean_object* v_x2_1627_){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; uint8_t v___x_1630_; 
v___x_1628_ = l_Lean_Name_toString(v_x1_1626_, v___x_1625_);
v___x_1629_ = l_Lean_Name_toString(v_x2_1627_, v___x_1625_);
v___x_1630_ = lean_string_dec_lt(v___x_1628_, v___x_1629_);
lean_dec_ref(v___x_1629_);
lean_dec_ref(v___x_1628_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0___boxed(lean_object* v___x_1631_, lean_object* v_x1_1632_, lean_object* v_x2_1633_){
_start:
{
uint8_t v___x_18512__boxed_1634_; uint8_t v_res_1635_; lean_object* v_r_1636_; 
v___x_18512__boxed_1634_ = lean_unbox(v___x_1631_);
v_res_1635_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_18512__boxed_1634_, v_x1_1632_, v_x2_1633_);
v_r_1636_ = lean_box(v_res_1635_);
return v_r_1636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(lean_object* v_as_1637_, lean_object* v_lo_1638_, lean_object* v_hi_1639_){
_start:
{
uint8_t v___x_1640_; 
v___x_1640_ = lean_nat_dec_lt(v_lo_1638_, v_hi_1639_);
if (v___x_1640_ == 0)
{
lean_dec(v_lo_1638_);
return v_as_1637_;
}
else
{
lean_object* v___x_1641_; lean_object* v___f_1642_; lean_object* v___x_1643_; lean_object* v_fst_1644_; lean_object* v_snd_1645_; uint8_t v___x_1646_; 
v___x_1641_ = lean_box(v___x_1640_);
v___f_1642_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1642_, 0, v___x_1641_);
lean_inc(v_lo_1638_);
v___x_1643_ = l_Array_qpartition___redArg(v_as_1637_, v___f_1642_, v_lo_1638_, v_hi_1639_);
v_fst_1644_ = lean_ctor_get(v___x_1643_, 0);
lean_inc(v_fst_1644_);
v_snd_1645_ = lean_ctor_get(v___x_1643_, 1);
lean_inc(v_snd_1645_);
lean_dec_ref(v___x_1643_);
v___x_1646_ = lean_nat_dec_le(v_hi_1639_, v_fst_1644_);
if (v___x_1646_ == 0)
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1647_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_snd_1645_, v_lo_1638_, v_fst_1644_);
v___x_1648_ = lean_unsigned_to_nat(1u);
v___x_1649_ = lean_nat_add(v_fst_1644_, v___x_1648_);
lean_dec(v_fst_1644_);
v_as_1637_ = v___x_1647_;
v_lo_1638_ = v___x_1649_;
goto _start;
}
else
{
lean_dec(v_fst_1644_);
lean_dec(v_lo_1638_);
return v_snd_1645_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___boxed(lean_object* v_as_1651_, lean_object* v_lo_1652_, lean_object* v_hi_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_as_1651_, v_lo_1652_, v_hi_1653_);
lean_dec(v_hi_1653_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___redArg(lean_object* v_a_1655_, lean_object* v_x_1656_){
_start:
{
if (lean_obj_tag(v_x_1656_) == 0)
{
lean_object* v___x_1657_; 
v___x_1657_ = lean_box(0);
return v___x_1657_;
}
else
{
lean_object* v_key_1658_; lean_object* v_value_1659_; lean_object* v_tail_1660_; uint8_t v___x_1661_; 
v_key_1658_ = lean_ctor_get(v_x_1656_, 0);
v_value_1659_ = lean_ctor_get(v_x_1656_, 1);
v_tail_1660_ = lean_ctor_get(v_x_1656_, 2);
v___x_1661_ = lean_name_eq(v_key_1658_, v_a_1655_);
if (v___x_1661_ == 0)
{
v_x_1656_ = v_tail_1660_;
goto _start;
}
else
{
lean_object* v___x_1663_; 
lean_inc(v_value_1659_);
v___x_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1663_, 0, v_value_1659_);
return v___x_1663_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___redArg___boxed(lean_object* v_a_1664_, lean_object* v_x_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___redArg(v_a_1664_, v_x_1665_);
lean_dec(v_x_1665_);
lean_dec(v_a_1664_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg(lean_object* v_m_1667_, lean_object* v_a_1668_){
_start:
{
lean_object* v_buckets_1669_; lean_object* v___x_1670_; uint64_t v___y_1672_; 
v_buckets_1669_ = lean_ctor_get(v_m_1667_, 1);
v___x_1670_ = lean_array_get_size(v_buckets_1669_);
if (lean_obj_tag(v_a_1668_) == 0)
{
uint64_t v___x_1686_; 
v___x_1686_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0);
v___y_1672_ = v___x_1686_;
goto v___jp_1671_;
}
else
{
uint64_t v_hash_1687_; 
v_hash_1687_ = lean_ctor_get_uint64(v_a_1668_, sizeof(void*)*2);
v___y_1672_ = v_hash_1687_;
goto v___jp_1671_;
}
v___jp_1671_:
{
uint64_t v___x_1673_; uint64_t v___x_1674_; uint64_t v_fold_1675_; uint64_t v___x_1676_; uint64_t v___x_1677_; uint64_t v___x_1678_; size_t v___x_1679_; size_t v___x_1680_; size_t v___x_1681_; size_t v___x_1682_; size_t v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1673_ = 32ULL;
v___x_1674_ = lean_uint64_shift_right(v___y_1672_, v___x_1673_);
v_fold_1675_ = lean_uint64_xor(v___y_1672_, v___x_1674_);
v___x_1676_ = 16ULL;
v___x_1677_ = lean_uint64_shift_right(v_fold_1675_, v___x_1676_);
v___x_1678_ = lean_uint64_xor(v_fold_1675_, v___x_1677_);
v___x_1679_ = lean_uint64_to_usize(v___x_1678_);
v___x_1680_ = lean_usize_of_nat(v___x_1670_);
v___x_1681_ = ((size_t)1ULL);
v___x_1682_ = lean_usize_sub(v___x_1680_, v___x_1681_);
v___x_1683_ = lean_usize_land(v___x_1679_, v___x_1682_);
v___x_1684_ = lean_array_uget_borrowed(v_buckets_1669_, v___x_1683_);
v___x_1685_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___redArg(v_a_1668_, v___x_1684_);
return v___x_1685_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg___boxed(lean_object* v_m_1688_, lean_object* v_a_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg(v_m_1688_, v_a_1689_);
lean_dec(v_a_1689_);
lean_dec_ref(v_m_1688_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(lean_object* v_keys_1691_, lean_object* v_vals_1692_, lean_object* v_i_1693_, lean_object* v_k_1694_){
_start:
{
lean_object* v___x_1695_; uint8_t v___x_1696_; 
v___x_1695_ = lean_array_get_size(v_keys_1691_);
v___x_1696_ = lean_nat_dec_lt(v_i_1693_, v___x_1695_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1697_; 
lean_dec(v_i_1693_);
v___x_1697_ = lean_box(0);
return v___x_1697_;
}
else
{
lean_object* v_k_x27_1698_; uint8_t v___x_1699_; 
v_k_x27_1698_ = lean_array_fget_borrowed(v_keys_1691_, v_i_1693_);
v___x_1699_ = lean_name_eq(v_k_1694_, v_k_x27_1698_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1700_ = lean_unsigned_to_nat(1u);
v___x_1701_ = lean_nat_add(v_i_1693_, v___x_1700_);
lean_dec(v_i_1693_);
v_i_1693_ = v___x_1701_;
goto _start;
}
else
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = lean_array_fget_borrowed(v_vals_1692_, v_i_1693_);
lean_dec(v_i_1693_);
lean_inc(v___x_1703_);
v___x_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1703_);
return v___x_1704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg___boxed(lean_object* v_keys_1705_, lean_object* v_vals_1706_, lean_object* v_i_1707_, lean_object* v_k_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_1705_, v_vals_1706_, v_i_1707_, v_k_1708_);
lean_dec(v_k_1708_);
lean_dec_ref(v_vals_1706_);
lean_dec_ref(v_keys_1705_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(lean_object* v_x_1710_, size_t v_x_1711_, lean_object* v_x_1712_){
_start:
{
if (lean_obj_tag(v_x_1710_) == 0)
{
lean_object* v_es_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1734_; 
v_es_1713_ = lean_ctor_get(v_x_1710_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_x_1710_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1715_ = v_x_1710_;
v_isShared_1716_ = v_isSharedCheck_1734_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_es_1713_);
lean_dec(v_x_1710_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1734_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1717_; size_t v___x_1718_; size_t v___x_1719_; size_t v___x_1720_; lean_object* v_j_1721_; lean_object* v___x_1722_; 
v___x_1717_ = lean_box(2);
v___x_1718_ = ((size_t)5ULL);
v___x_1719_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1);
v___x_1720_ = lean_usize_land(v_x_1711_, v___x_1719_);
v_j_1721_ = lean_usize_to_nat(v___x_1720_);
v___x_1722_ = lean_array_get(v___x_1717_, v_es_1713_, v_j_1721_);
lean_dec(v_j_1721_);
lean_dec_ref(v_es_1713_);
switch(lean_obj_tag(v___x_1722_))
{
case 0:
{
lean_object* v_key_1723_; lean_object* v_val_1724_; uint8_t v___x_1725_; 
v_key_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_key_1723_);
v_val_1724_ = lean_ctor_get(v___x_1722_, 1);
lean_inc(v_val_1724_);
lean_dec_ref(v___x_1722_);
v___x_1725_ = lean_name_eq(v_x_1712_, v_key_1723_);
lean_dec(v_key_1723_);
if (v___x_1725_ == 0)
{
lean_object* v___x_1726_; 
lean_dec(v_val_1724_);
lean_del_object(v___x_1715_);
v___x_1726_ = lean_box(0);
return v___x_1726_;
}
else
{
lean_object* v___x_1728_; 
if (v_isShared_1716_ == 0)
{
lean_ctor_set_tag(v___x_1715_, 1);
lean_ctor_set(v___x_1715_, 0, v_val_1724_);
v___x_1728_ = v___x_1715_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_val_1724_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
case 1:
{
lean_object* v_node_1730_; size_t v___x_1731_; 
lean_del_object(v___x_1715_);
v_node_1730_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_node_1730_);
lean_dec_ref(v___x_1722_);
v___x_1731_ = lean_usize_shift_right(v_x_1711_, v___x_1718_);
v_x_1710_ = v_node_1730_;
v_x_1711_ = v___x_1731_;
goto _start;
}
default: 
{
lean_object* v___x_1733_; 
lean_del_object(v___x_1715_);
v___x_1733_ = lean_box(0);
return v___x_1733_;
}
}
}
}
else
{
lean_object* v_ks_1735_; lean_object* v_vs_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v_ks_1735_ = lean_ctor_get(v_x_1710_, 0);
lean_inc_ref(v_ks_1735_);
v_vs_1736_ = lean_ctor_get(v_x_1710_, 1);
lean_inc_ref(v_vs_1736_);
lean_dec_ref(v_x_1710_);
v___x_1737_ = lean_unsigned_to_nat(0u);
v___x_1738_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_ks_1735_, v_vs_1736_, v___x_1737_, v_x_1712_);
lean_dec_ref(v_vs_1736_);
lean_dec_ref(v_ks_1735_);
return v___x_1738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_x_1739_, lean_object* v_x_1740_, lean_object* v_x_1741_){
_start:
{
size_t v_x_18629__boxed_1742_; lean_object* v_res_1743_; 
v_x_18629__boxed_1742_ = lean_unbox_usize(v_x_1740_);
lean_dec(v_x_1740_);
v_res_1743_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_1739_, v_x_18629__boxed_1742_, v_x_1741_);
lean_dec(v_x_1741_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(lean_object* v_x_1744_, lean_object* v_x_1745_){
_start:
{
uint64_t v___y_1747_; 
if (lean_obj_tag(v_x_1745_) == 0)
{
uint64_t v___x_1750_; 
v___x_1750_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0);
v___y_1747_ = v___x_1750_;
goto v___jp_1746_;
}
else
{
uint64_t v_hash_1751_; 
v_hash_1751_ = lean_ctor_get_uint64(v_x_1745_, sizeof(void*)*2);
v___y_1747_ = v_hash_1751_;
goto v___jp_1746_;
}
v___jp_1746_:
{
size_t v___x_1748_; lean_object* v___x_1749_; 
v___x_1748_ = lean_uint64_to_usize(v___y_1747_);
v___x_1749_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_1744_, v___x_1748_, v_x_1745_);
return v___x_1749_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg___boxed(lean_object* v_x_1752_, lean_object* v_x_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_1752_, v_x_1753_);
lean_dec(v_x_1753_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___redArg(lean_object* v_x_1755_, lean_object* v_x_1756_){
_start:
{
uint8_t v_stage_u2081_1757_; 
v_stage_u2081_1757_ = lean_ctor_get_uint8(v_x_1755_, sizeof(void*)*2);
if (v_stage_u2081_1757_ == 0)
{
lean_object* v_map_u2081_1758_; lean_object* v_map_u2082_1759_; lean_object* v___x_1760_; 
v_map_u2081_1758_ = lean_ctor_get(v_x_1755_, 0);
lean_inc_ref(v_map_u2081_1758_);
v_map_u2082_1759_ = lean_ctor_get(v_x_1755_, 1);
lean_inc_ref(v_map_u2082_1759_);
lean_dec_ref(v_x_1755_);
v___x_1760_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg(v_map_u2081_1758_, v_x_1756_);
lean_dec_ref(v_map_u2081_1758_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_map_u2082_1759_, v_x_1756_);
return v___x_1761_;
}
else
{
lean_dec_ref(v_map_u2082_1759_);
return v___x_1760_;
}
}
else
{
lean_object* v_map_u2081_1762_; lean_object* v___x_1763_; 
v_map_u2081_1762_ = lean_ctor_get(v_x_1755_, 0);
lean_inc_ref(v_map_u2081_1762_);
lean_dec_ref(v_x_1755_);
v___x_1763_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg(v_map_u2081_1762_, v_x_1756_);
lean_dec_ref(v_map_u2081_1762_);
return v___x_1763_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___redArg___boxed(lean_object* v_x_1764_, lean_object* v_x_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___redArg(v_x_1764_, v_x_1765_);
lean_dec(v_x_1765_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__14(lean_object* v_a_1767_, lean_object* v_a_1768_){
_start:
{
if (lean_obj_tag(v_a_1767_) == 0)
{
lean_object* v___x_1769_; 
v___x_1769_ = l_List_reverse___redArg(v_a_1768_);
return v___x_1769_;
}
else
{
lean_object* v_head_1770_; lean_object* v_tail_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1780_; 
v_head_1770_ = lean_ctor_get(v_a_1767_, 0);
v_tail_1771_ = lean_ctor_get(v_a_1767_, 1);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_a_1767_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1773_ = v_a_1767_;
v_isShared_1774_ = v_isSharedCheck_1780_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_tail_1771_);
lean_inc(v_head_1770_);
lean_dec(v_a_1767_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1780_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1775_; lean_object* v___x_1777_; 
v___x_1775_ = l_Lean_Level_param___override(v_head_1770_);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 1, v_a_1768_);
lean_ctor_set(v___x_1773_, 0, v___x_1775_);
v___x_1777_ = v___x_1773_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1775_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_a_1768_);
v___x_1777_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
v_a_1767_ = v_tail_1771_;
v_a_1768_ = v___x_1777_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg(lean_object* v_t_1781_, lean_object* v_k_1782_){
_start:
{
if (lean_obj_tag(v_t_1781_) == 0)
{
lean_object* v_k_1783_; lean_object* v_v_1784_; lean_object* v_l_1785_; lean_object* v_r_1786_; uint8_t v___x_1787_; 
v_k_1783_ = lean_ctor_get(v_t_1781_, 1);
v_v_1784_ = lean_ctor_get(v_t_1781_, 2);
v_l_1785_ = lean_ctor_get(v_t_1781_, 3);
v_r_1786_ = lean_ctor_get(v_t_1781_, 4);
v___x_1787_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1782_, v_k_1783_);
switch(v___x_1787_)
{
case 0:
{
v_t_1781_ = v_l_1785_;
goto _start;
}
case 1:
{
lean_object* v___x_1789_; 
lean_inc(v_v_1784_);
v___x_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1789_, 0, v_v_1784_);
return v___x_1789_;
}
default: 
{
v_t_1781_ = v_r_1786_;
goto _start;
}
}
}
else
{
lean_object* v___x_1791_; 
v___x_1791_ = lean_box(0);
return v___x_1791_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg___boxed(lean_object* v_t_1792_, lean_object* v_k_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg(v_t_1792_, v_k_1793_);
lean_dec(v_k_1793_);
lean_dec(v_t_1792_);
return v_res_1794_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(lean_object* v_x1_1795_, lean_object* v_x2_1796_){
_start:
{
lean_object* v_fst_1797_; lean_object* v_fst_1798_; uint8_t v___x_1799_; 
v_fst_1797_ = lean_ctor_get(v_x1_1795_, 0);
v_fst_1798_ = lean_ctor_get(v_x2_1796_, 0);
v___x_1799_ = l_Lean_Name_quickLt(v_fst_1797_, v_fst_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0___boxed(lean_object* v_x1_1800_, lean_object* v_x2_1801_){
_start:
{
uint8_t v_res_1802_; lean_object* v_r_1803_; 
v_res_1802_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_x1_1800_, v_x2_1801_);
lean_dec_ref(v_x2_1801_);
lean_dec_ref(v_x1_1800_);
v_r_1803_ = lean_box(v_res_1802_);
return v_r_1803_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(lean_object* v_as_1804_, lean_object* v_k_1805_, lean_object* v_x_1806_, lean_object* v_x_1807_){
_start:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v_m_1810_; lean_object* v_a_1811_; uint8_t v___x_1812_; 
v___x_1808_ = lean_nat_add(v_x_1806_, v_x_1807_);
v___x_1809_ = lean_unsigned_to_nat(1u);
v_m_1810_ = lean_nat_shiftr(v___x_1808_, v___x_1809_);
lean_dec(v___x_1808_);
v_a_1811_ = lean_array_fget_borrowed(v_as_1804_, v_m_1810_);
v___x_1812_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_a_1811_, v_k_1805_);
if (v___x_1812_ == 0)
{
uint8_t v___x_1813_; 
lean_dec(v_x_1807_);
v___x_1813_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_k_1805_, v_a_1811_);
if (v___x_1813_ == 0)
{
lean_object* v___x_1814_; 
lean_dec(v_m_1810_);
lean_dec(v_x_1806_);
lean_inc(v_a_1811_);
v___x_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1814_, 0, v_a_1811_);
return v___x_1814_;
}
else
{
lean_object* v___x_1815_; uint8_t v___x_1816_; 
v___x_1815_ = lean_unsigned_to_nat(0u);
v___x_1816_ = lean_nat_dec_eq(v_m_1810_, v___x_1815_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1817_; uint8_t v___x_1818_; 
v___x_1817_ = lean_nat_sub(v_m_1810_, v___x_1809_);
lean_dec(v_m_1810_);
v___x_1818_ = lean_nat_dec_lt(v___x_1817_, v_x_1806_);
if (v___x_1818_ == 0)
{
v_x_1807_ = v___x_1817_;
goto _start;
}
else
{
lean_object* v___x_1820_; 
lean_dec(v___x_1817_);
lean_dec(v_x_1806_);
v___x_1820_ = lean_box(0);
return v___x_1820_;
}
}
else
{
lean_object* v___x_1821_; 
lean_dec(v_m_1810_);
lean_dec(v_x_1806_);
v___x_1821_ = lean_box(0);
return v___x_1821_;
}
}
}
else
{
lean_object* v___x_1822_; uint8_t v___x_1823_; 
lean_dec(v_x_1806_);
v___x_1822_ = lean_nat_add(v_m_1810_, v___x_1809_);
lean_dec(v_m_1810_);
v___x_1823_ = lean_nat_dec_le(v___x_1822_, v_x_1807_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; 
lean_dec(v___x_1822_);
lean_dec(v_x_1807_);
v___x_1824_ = lean_box(0);
return v___x_1824_;
}
else
{
v_x_1806_ = v___x_1822_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___boxed(lean_object* v_as_1826_, lean_object* v_k_1827_, lean_object* v_x_1828_, lean_object* v_x_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_1826_, v_k_1827_, v_x_1828_, v_x_1829_);
lean_dec_ref(v_k_1827_);
lean_dec_ref(v_as_1826_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(lean_object* v_tac_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v___x_1835_; lean_object* v_env_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1835_ = lean_st_ref_get(v___y_1833_);
v_env_1839_ = lean_ctor_get(v___x_1835_, 0);
lean_inc_ref(v_env_1839_);
lean_dec(v___x_1835_);
v___x_1840_ = lean_box(1);
v___x_1841_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1839_, v_tac_1832_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v___x_1842_; lean_object* v_toEnvExtension_1843_; lean_object* v_asyncMode_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1842_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_1843_ = lean_ctor_get(v___x_1842_, 0);
lean_inc_ref(v_toEnvExtension_1843_);
v_asyncMode_1844_ = lean_ctor_get(v_toEnvExtension_1843_, 2);
lean_inc(v_asyncMode_1844_);
lean_dec_ref(v_toEnvExtension_1843_);
v___x_1845_ = lean_box(0);
v___x_1846_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1840_, v___x_1842_, v_env_1839_, v_asyncMode_1844_, v___x_1845_);
lean_dec(v_asyncMode_1844_);
v___x_1847_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1846_, v_tac_1832_);
lean_dec(v_tac_1832_);
lean_dec(v___x_1846_);
v___x_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
return v___x_1848_;
}
else
{
lean_object* v_val_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1877_; 
v_val_1849_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1851_ = v___x_1841_;
v_isShared_1852_ = v_isSharedCheck_1877_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_val_1849_);
lean_dec(v___x_1841_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1877_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1853_; uint8_t v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; uint8_t v___x_1858_; 
v___x_1853_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v___x_1854_ = 0;
v___x_1855_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1840_, v___x_1853_, v_env_1839_, v_val_1849_, v___x_1854_);
lean_dec(v_val_1849_);
lean_dec_ref(v_env_1839_);
v___x_1856_ = lean_unsigned_to_nat(0u);
v___x_1857_ = lean_array_get_size(v___x_1855_);
v___x_1858_ = lean_nat_dec_lt(v___x_1856_, v___x_1857_);
if (v___x_1858_ == 0)
{
lean_dec_ref(v___x_1855_);
lean_del_object(v___x_1851_);
lean_dec(v_tac_1832_);
goto v___jp_1836_;
}
else
{
lean_object* v___x_1859_; lean_object* v___x_1860_; uint8_t v___x_1861_; 
v___x_1859_ = lean_unsigned_to_nat(1u);
v___x_1860_ = lean_nat_sub(v___x_1857_, v___x_1859_);
v___x_1861_ = lean_nat_dec_le(v___x_1856_, v___x_1860_);
if (v___x_1861_ == 0)
{
lean_dec(v___x_1860_);
lean_dec_ref(v___x_1855_);
lean_del_object(v___x_1851_);
lean_dec(v_tac_1832_);
goto v___jp_1836_;
}
else
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1862_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0));
v___x_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1863_, 0, v_tac_1832_);
lean_ctor_set(v___x_1863_, 1, v___x_1862_);
v___x_1864_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v___x_1855_, v___x_1863_, v___x_1856_, v___x_1860_);
lean_dec_ref(v___x_1863_);
lean_dec_ref(v___x_1855_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_del_object(v___x_1851_);
goto v___jp_1836_;
}
else
{
lean_object* v_val_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1876_; 
v_val_1865_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1867_ = v___x_1864_;
v_isShared_1868_ = v_isSharedCheck_1876_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_val_1865_);
lean_dec(v___x_1864_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1876_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v_snd_1869_; lean_object* v___x_1871_; 
v_snd_1869_ = lean_ctor_get(v_val_1865_, 1);
lean_inc(v_snd_1869_);
lean_dec(v_val_1865_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 0, v_snd_1869_);
v___x_1871_ = v___x_1867_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_snd_1869_);
v___x_1871_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
lean_object* v___x_1873_; 
if (v_isShared_1852_ == 0)
{
lean_ctor_set_tag(v___x_1851_, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1871_);
v___x_1873_ = v___x_1851_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v___x_1871_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
}
}
}
}
}
}
v___jp_1836_:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1837_ = lean_box(0);
v___x_1838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1837_);
return v___x_1838_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___boxed(lean_object* v_tac_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_1878_, v___y_1879_);
lean_dec(v___y_1879_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(lean_object* v_k_1882_, lean_object* v_v_1883_, lean_object* v_t_1884_){
_start:
{
if (lean_obj_tag(v_t_1884_) == 0)
{
lean_object* v_size_1885_; lean_object* v_k_1886_; lean_object* v_v_1887_; lean_object* v_l_1888_; lean_object* v_r_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_2170_; 
v_size_1885_ = lean_ctor_get(v_t_1884_, 0);
v_k_1886_ = lean_ctor_get(v_t_1884_, 1);
v_v_1887_ = lean_ctor_get(v_t_1884_, 2);
v_l_1888_ = lean_ctor_get(v_t_1884_, 3);
v_r_1889_ = lean_ctor_get(v_t_1884_, 4);
v_isSharedCheck_2170_ = !lean_is_exclusive(v_t_1884_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_1891_ = v_t_1884_;
v_isShared_1892_ = v_isSharedCheck_2170_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_r_1889_);
lean_inc(v_l_1888_);
lean_inc(v_v_1887_);
lean_inc(v_k_1886_);
lean_inc(v_size_1885_);
lean_dec(v_t_1884_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_2170_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
uint8_t v___x_1893_; 
v___x_1893_ = lean_nat_dec_lt(v_k_1882_, v_k_1886_);
if (v___x_1893_ == 0)
{
uint8_t v___x_1894_; 
v___x_1894_ = lean_nat_dec_eq(v_k_1882_, v_k_1886_);
if (v___x_1894_ == 0)
{
lean_object* v_impl_1895_; lean_object* v___x_1896_; 
lean_dec(v_size_1885_);
v_impl_1895_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_k_1882_, v_v_1883_, v_r_1889_);
v___x_1896_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1888_) == 0)
{
lean_object* v_size_1897_; lean_object* v_size_1898_; lean_object* v_k_1899_; lean_object* v_v_1900_; lean_object* v_l_1901_; lean_object* v_r_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; uint8_t v___x_1905_; 
v_size_1897_ = lean_ctor_get(v_l_1888_, 0);
v_size_1898_ = lean_ctor_get(v_impl_1895_, 0);
lean_inc(v_size_1898_);
v_k_1899_ = lean_ctor_get(v_impl_1895_, 1);
lean_inc(v_k_1899_);
v_v_1900_ = lean_ctor_get(v_impl_1895_, 2);
lean_inc(v_v_1900_);
v_l_1901_ = lean_ctor_get(v_impl_1895_, 3);
lean_inc(v_l_1901_);
v_r_1902_ = lean_ctor_get(v_impl_1895_, 4);
lean_inc(v_r_1902_);
v___x_1903_ = lean_unsigned_to_nat(3u);
v___x_1904_ = lean_nat_mul(v___x_1903_, v_size_1897_);
v___x_1905_ = lean_nat_dec_lt(v___x_1904_, v_size_1898_);
lean_dec(v___x_1904_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1909_; 
lean_dec(v_r_1902_);
lean_dec(v_l_1901_);
lean_dec(v_v_1900_);
lean_dec(v_k_1899_);
v___x_1906_ = lean_nat_add(v___x_1896_, v_size_1897_);
v___x_1907_ = lean_nat_add(v___x_1906_, v_size_1898_);
lean_dec(v_size_1898_);
lean_dec(v___x_1906_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 4, v_impl_1895_);
lean_ctor_set(v___x_1891_, 0, v___x_1907_);
v___x_1909_ = v___x_1891_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
lean_ctor_set(v_reuseFailAlloc_1910_, 1, v_k_1886_);
lean_ctor_set(v_reuseFailAlloc_1910_, 2, v_v_1887_);
lean_ctor_set(v_reuseFailAlloc_1910_, 3, v_l_1888_);
lean_ctor_set(v_reuseFailAlloc_1910_, 4, v_impl_1895_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
else
{
lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1974_; 
v_isSharedCheck_1974_ = !lean_is_exclusive(v_impl_1895_);
if (v_isSharedCheck_1974_ == 0)
{
lean_object* v_unused_1975_; lean_object* v_unused_1976_; lean_object* v_unused_1977_; lean_object* v_unused_1978_; lean_object* v_unused_1979_; 
v_unused_1975_ = lean_ctor_get(v_impl_1895_, 4);
lean_dec(v_unused_1975_);
v_unused_1976_ = lean_ctor_get(v_impl_1895_, 3);
lean_dec(v_unused_1976_);
v_unused_1977_ = lean_ctor_get(v_impl_1895_, 2);
lean_dec(v_unused_1977_);
v_unused_1978_ = lean_ctor_get(v_impl_1895_, 1);
lean_dec(v_unused_1978_);
v_unused_1979_ = lean_ctor_get(v_impl_1895_, 0);
lean_dec(v_unused_1979_);
v___x_1912_ = v_impl_1895_;
v_isShared_1913_ = v_isSharedCheck_1974_;
goto v_resetjp_1911_;
}
else
{
lean_dec(v_impl_1895_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1974_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v_size_1914_; lean_object* v_k_1915_; lean_object* v_v_1916_; lean_object* v_l_1917_; lean_object* v_r_1918_; lean_object* v_size_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; uint8_t v___x_1922_; 
v_size_1914_ = lean_ctor_get(v_l_1901_, 0);
v_k_1915_ = lean_ctor_get(v_l_1901_, 1);
v_v_1916_ = lean_ctor_get(v_l_1901_, 2);
v_l_1917_ = lean_ctor_get(v_l_1901_, 3);
v_r_1918_ = lean_ctor_get(v_l_1901_, 4);
v_size_1919_ = lean_ctor_get(v_r_1902_, 0);
v___x_1920_ = lean_unsigned_to_nat(2u);
v___x_1921_ = lean_nat_mul(v___x_1920_, v_size_1919_);
v___x_1922_ = lean_nat_dec_lt(v_size_1914_, v___x_1921_);
lean_dec(v___x_1921_);
if (v___x_1922_ == 0)
{
lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1950_; 
lean_inc(v_r_1918_);
lean_inc(v_l_1917_);
lean_inc(v_v_1916_);
lean_inc(v_k_1915_);
v_isSharedCheck_1950_ = !lean_is_exclusive(v_l_1901_);
if (v_isSharedCheck_1950_ == 0)
{
lean_object* v_unused_1951_; lean_object* v_unused_1952_; lean_object* v_unused_1953_; lean_object* v_unused_1954_; lean_object* v_unused_1955_; 
v_unused_1951_ = lean_ctor_get(v_l_1901_, 4);
lean_dec(v_unused_1951_);
v_unused_1952_ = lean_ctor_get(v_l_1901_, 3);
lean_dec(v_unused_1952_);
v_unused_1953_ = lean_ctor_get(v_l_1901_, 2);
lean_dec(v_unused_1953_);
v_unused_1954_ = lean_ctor_get(v_l_1901_, 1);
lean_dec(v_unused_1954_);
v_unused_1955_ = lean_ctor_get(v_l_1901_, 0);
lean_dec(v_unused_1955_);
v___x_1924_ = v_l_1901_;
v_isShared_1925_ = v_isSharedCheck_1950_;
goto v_resetjp_1923_;
}
else
{
lean_dec(v_l_1901_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1950_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1940_; 
v___x_1926_ = lean_nat_add(v___x_1896_, v_size_1897_);
v___x_1927_ = lean_nat_add(v___x_1926_, v_size_1898_);
lean_dec(v_size_1898_);
if (lean_obj_tag(v_l_1917_) == 0)
{
lean_object* v_size_1948_; 
v_size_1948_ = lean_ctor_get(v_l_1917_, 0);
lean_inc(v_size_1948_);
v___y_1940_ = v_size_1948_;
goto v___jp_1939_;
}
else
{
lean_object* v___x_1949_; 
v___x_1949_ = lean_unsigned_to_nat(0u);
v___y_1940_ = v___x_1949_;
goto v___jp_1939_;
}
v___jp_1928_:
{
lean_object* v___x_1932_; lean_object* v___x_1934_; 
v___x_1932_ = lean_nat_add(v___y_1930_, v___y_1931_);
lean_dec(v___y_1931_);
lean_dec(v___y_1930_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 4, v_r_1902_);
lean_ctor_set(v___x_1924_, 3, v_r_1918_);
lean_ctor_set(v___x_1924_, 2, v_v_1900_);
lean_ctor_set(v___x_1924_, 1, v_k_1899_);
lean_ctor_set(v___x_1924_, 0, v___x_1932_);
v___x_1934_ = v___x_1924_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1932_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_k_1899_);
lean_ctor_set(v_reuseFailAlloc_1938_, 2, v_v_1900_);
lean_ctor_set(v_reuseFailAlloc_1938_, 3, v_r_1918_);
lean_ctor_set(v_reuseFailAlloc_1938_, 4, v_r_1902_);
v___x_1934_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
lean_object* v___x_1936_; 
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 4, v___x_1934_);
lean_ctor_set(v___x_1912_, 3, v___y_1929_);
lean_ctor_set(v___x_1912_, 2, v_v_1916_);
lean_ctor_set(v___x_1912_, 1, v_k_1915_);
lean_ctor_set(v___x_1912_, 0, v___x_1927_);
v___x_1936_ = v___x_1912_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1927_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v_k_1915_);
lean_ctor_set(v_reuseFailAlloc_1937_, 2, v_v_1916_);
lean_ctor_set(v_reuseFailAlloc_1937_, 3, v___y_1929_);
lean_ctor_set(v_reuseFailAlloc_1937_, 4, v___x_1934_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
v___jp_1939_:
{
lean_object* v___x_1941_; lean_object* v___x_1943_; 
v___x_1941_ = lean_nat_add(v___x_1926_, v___y_1940_);
lean_dec(v___y_1940_);
lean_dec(v___x_1926_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 4, v_l_1917_);
lean_ctor_set(v___x_1891_, 0, v___x_1941_);
v___x_1943_ = v___x_1891_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1941_);
lean_ctor_set(v_reuseFailAlloc_1947_, 1, v_k_1886_);
lean_ctor_set(v_reuseFailAlloc_1947_, 2, v_v_1887_);
lean_ctor_set(v_reuseFailAlloc_1947_, 3, v_l_1888_);
lean_ctor_set(v_reuseFailAlloc_1947_, 4, v_l_1917_);
v___x_1943_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
lean_object* v___x_1944_; 
v___x_1944_ = lean_nat_add(v___x_1896_, v_size_1919_);
if (lean_obj_tag(v_r_1918_) == 0)
{
lean_object* v_size_1945_; 
v_size_1945_ = lean_ctor_get(v_r_1918_, 0);
lean_inc(v_size_1945_);
v___y_1929_ = v___x_1943_;
v___y_1930_ = v___x_1944_;
v___y_1931_ = v_size_1945_;
goto v___jp_1928_;
}
else
{
lean_object* v___x_1946_; 
v___x_1946_ = lean_unsigned_to_nat(0u);
v___y_1929_ = v___x_1943_;
v___y_1930_ = v___x_1944_;
v___y_1931_ = v___x_1946_;
goto v___jp_1928_;
}
}
}
}
}
else
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1960_; 
lean_del_object(v___x_1891_);
v___x_1956_ = lean_nat_add(v___x_1896_, v_size_1897_);
v___x_1957_ = lean_nat_add(v___x_1956_, v_size_1898_);
lean_dec(v_size_1898_);
v___x_1958_ = lean_nat_add(v___x_1956_, v_size_1914_);
lean_dec(v___x_1956_);
lean_inc_ref(v_l_1888_);
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 4, v_l_1901_);
lean_ctor_set(v___x_1912_, 3, v_l_1888_);
lean_ctor_set(v___x_1912_, 2, v_v_1887_);
lean_ctor_set(v___x_1912_, 1, v_k_1886_);
lean_ctor_set(v___x_1912_, 0, v___x_1958_);
v___x_1960_ = v___x_1912_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1958_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_k_1886_);
lean_ctor_set(v_reuseFailAlloc_1973_, 2, v_v_1887_);
lean_ctor_set(v_reuseFailAlloc_1973_, 3, v_l_1888_);
lean_ctor_set(v_reuseFailAlloc_1973_, 4, v_l_1901_);
v___x_1960_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1967_; 
v_isSharedCheck_1967_ = !lean_is_exclusive(v_l_1888_);
if (v_isSharedCheck_1967_ == 0)
{
lean_object* v_unused_1968_; lean_object* v_unused_1969_; lean_object* v_unused_1970_; lean_object* v_unused_1971_; lean_object* v_unused_1972_; 
v_unused_1968_ = lean_ctor_get(v_l_1888_, 4);
lean_dec(v_unused_1968_);
v_unused_1969_ = lean_ctor_get(v_l_1888_, 3);
lean_dec(v_unused_1969_);
v_unused_1970_ = lean_ctor_get(v_l_1888_, 2);
lean_dec(v_unused_1970_);
v_unused_1971_ = lean_ctor_get(v_l_1888_, 1);
lean_dec(v_unused_1971_);
v_unused_1972_ = lean_ctor_get(v_l_1888_, 0);
lean_dec(v_unused_1972_);
v___x_1962_ = v_l_1888_;
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
else
{
lean_dec(v_l_1888_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1965_; 
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 4, v_r_1902_);
lean_ctor_set(v___x_1962_, 3, v___x_1960_);
lean_ctor_set(v___x_1962_, 2, v_v_1900_);
lean_ctor_set(v___x_1962_, 1, v_k_1899_);
lean_ctor_set(v___x_1962_, 0, v___x_1957_);
v___x_1965_ = v___x_1962_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1957_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v_k_1899_);
lean_ctor_set(v_reuseFailAlloc_1966_, 2, v_v_1900_);
lean_ctor_set(v_reuseFailAlloc_1966_, 3, v___x_1960_);
lean_ctor_set(v_reuseFailAlloc_1966_, 4, v_r_1902_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1980_; 
v_l_1980_ = lean_ctor_get(v_impl_1895_, 3);
lean_inc(v_l_1980_);
if (lean_obj_tag(v_l_1980_) == 0)
{
lean_object* v_r_1981_; lean_object* v_k_1982_; lean_object* v_v_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2006_; 
v_r_1981_ = lean_ctor_get(v_impl_1895_, 4);
v_k_1982_ = lean_ctor_get(v_impl_1895_, 1);
v_v_1983_ = lean_ctor_get(v_impl_1895_, 2);
v_isSharedCheck_2006_ = !lean_is_exclusive(v_impl_1895_);
if (v_isSharedCheck_2006_ == 0)
{
lean_object* v_unused_2007_; lean_object* v_unused_2008_; 
v_unused_2007_ = lean_ctor_get(v_impl_1895_, 3);
lean_dec(v_unused_2007_);
v_unused_2008_ = lean_ctor_get(v_impl_1895_, 0);
lean_dec(v_unused_2008_);
v___x_1985_ = v_impl_1895_;
v_isShared_1986_ = v_isSharedCheck_2006_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_r_1981_);
lean_inc(v_v_1983_);
lean_inc(v_k_1982_);
lean_dec(v_impl_1895_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2006_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v_k_1987_; lean_object* v_v_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2002_; 
v_k_1987_ = lean_ctor_get(v_l_1980_, 1);
v_v_1988_ = lean_ctor_get(v_l_1980_, 2);
v_isSharedCheck_2002_ = !lean_is_exclusive(v_l_1980_);
if (v_isSharedCheck_2002_ == 0)
{
lean_object* v_unused_2003_; lean_object* v_unused_2004_; lean_object* v_unused_2005_; 
v_unused_2003_ = lean_ctor_get(v_l_1980_, 4);
lean_dec(v_unused_2003_);
v_unused_2004_ = lean_ctor_get(v_l_1980_, 3);
lean_dec(v_unused_2004_);
v_unused_2005_ = lean_ctor_get(v_l_1980_, 0);
lean_dec(v_unused_2005_);
v___x_1990_ = v_l_1980_;
v_isShared_1991_ = v_isSharedCheck_2002_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_v_1988_);
lean_inc(v_k_1987_);
lean_dec(v_l_1980_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2002_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1992_; lean_object* v___x_1994_; 
v___x_1992_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1981_, 2);
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 4, v_r_1981_);
lean_ctor_set(v___x_1990_, 3, v_r_1981_);
lean_ctor_set(v___x_1990_, 2, v_v_1887_);
lean_ctor_set(v___x_1990_, 1, v_k_1886_);
lean_ctor_set(v___x_1990_, 0, v___x_1896_);
v___x_1994_ = v___x_1990_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1896_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v_k_1886_);
lean_ctor_set(v_reuseFailAlloc_2001_, 2, v_v_1887_);
lean_ctor_set(v_reuseFailAlloc_2001_, 3, v_r_1981_);
lean_ctor_set(v_reuseFailAlloc_2001_, 4, v_r_1981_);
v___x_1994_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
lean_object* v___x_1996_; 
lean_inc(v_r_1981_);
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 3, v_r_1981_);
lean_ctor_set(v___x_1985_, 0, v___x_1896_);
v___x_1996_ = v___x_1985_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1896_);
lean_ctor_set(v_reuseFailAlloc_2000_, 1, v_k_1982_);
lean_ctor_set(v_reuseFailAlloc_2000_, 2, v_v_1983_);
lean_ctor_set(v_reuseFailAlloc_2000_, 3, v_r_1981_);
lean_ctor_set(v_reuseFailAlloc_2000_, 4, v_r_1981_);
v___x_1996_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
lean_object* v___x_1998_; 
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 4, v___x_1996_);
lean_ctor_set(v___x_1891_, 3, v___x_1994_);
lean_ctor_set(v___x_1891_, 2, v_v_1988_);
lean_ctor_set(v___x_1891_, 1, v_k_1987_);
lean_ctor_set(v___x_1891_, 0, v___x_1992_);
v___x_1998_ = v___x_1891_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1992_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_k_1987_);
lean_ctor_set(v_reuseFailAlloc_1999_, 2, v_v_1988_);
lean_ctor_set(v_reuseFailAlloc_1999_, 3, v___x_1994_);
lean_ctor_set(v_reuseFailAlloc_1999_, 4, v___x_1996_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
}
}
else
{
lean_object* v_r_2009_; 
v_r_2009_ = lean_ctor_get(v_impl_1895_, 4);
lean_inc(v_r_2009_);
if (lean_obj_tag(v_r_2009_) == 0)
{
lean_object* v_k_2010_; lean_object* v_v_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2022_; 
v_k_2010_ = lean_ctor_get(v_impl_1895_, 1);
v_v_2011_ = lean_ctor_get(v_impl_1895_, 2);
v_isSharedCheck_2022_ = !lean_is_exclusive(v_impl_1895_);
if (v_isSharedCheck_2022_ == 0)
{
lean_object* v_unused_2023_; lean_object* v_unused_2024_; lean_object* v_unused_2025_; 
v_unused_2023_ = lean_ctor_get(v_impl_1895_, 4);
lean_dec(v_unused_2023_);
v_unused_2024_ = lean_ctor_get(v_impl_1895_, 3);
lean_dec(v_unused_2024_);
v_unused_2025_ = lean_ctor_get(v_impl_1895_, 0);
lean_dec(v_unused_2025_);
v___x_2013_ = v_impl_1895_;
v_isShared_2014_ = v_isSharedCheck_2022_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_v_2011_);
lean_inc(v_k_2010_);
lean_dec(v_impl_1895_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2022_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2015_; lean_object* v___x_2017_; 
v___x_2015_ = lean_unsigned_to_nat(3u);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 4, v_l_1980_);
lean_ctor_set(v___x_2013_, 2, v_v_1887_);
lean_ctor_set(v___x_2013_, 1, v_k_1886_);
lean_ctor_set(v___x_2013_, 0, v___x_1896_);
v___x_2017_ = v___x_2013_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_1896_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v_k_1886_);
lean_ctor_set(v_reuseFailAlloc_2021_, 2, v_v_1887_);
lean_ctor_set(v_reuseFailAlloc_2021_, 3, v_l_1980_);
lean_ctor_set(v_reuseFailAlloc_2021_, 4, v_l_1980_);
v___x_2017_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
lean_object* v___x_2019_; 
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 4, v_r_2009_);
lean_ctor_set(v___x_1891_, 3, v___x_2017_);
lean_ctor_set(v___x_1891_, 2, v_v_2011_);
lean_ctor_set(v___x_1891_, 1, v_k_2010_);
lean_ctor_set(v___x_1891_, 0, v___x_2015_);
v___x_2019_ = v___x_1891_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2015_);
lean_ctor_set(v_reuseFailAlloc_2020_, 1, v_k_2010_);
lean_ctor_set(v_reuseFailAlloc_2020_, 2, v_v_2011_);
lean_ctor_set(v_reuseFailAlloc_2020_, 3, v___x_2017_);
lean_ctor_set(v_reuseFailAlloc_2020_, 4, v_r_2009_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
else
{
lean_object* v___x_2026_; lean_object* v___x_2028_; 
v___x_2026_ = lean_unsigned_to_nat(2u);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 4, v_impl_1895_);
lean_ctor_set(v___x_1891_, 3, v_r_2009_);
lean_ctor_set(v___x_1891_, 0, v___x_2026_);
v___x_2028_ = v___x_1891_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
lean_ctor_set(v_reuseFailAlloc_2029_, 1, v_k_1886_);
lean_ctor_set(v_reuseFailAlloc_2029_, 2, v_v_1887_);
lean_ctor_set(v_reuseFailAlloc_2029_, 3, v_r_2009_);
lean_ctor_set(v_reuseFailAlloc_2029_, 4, v_impl_1895_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
}
else
{
lean_object* v___x_2031_; 
lean_dec(v_v_1887_);
lean_dec(v_k_1886_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 2, v_v_1883_);
lean_ctor_set(v___x_1891_, 1, v_k_1882_);
v___x_2031_ = v___x_1891_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_size_1885_);
lean_ctor_set(v_reuseFailAlloc_2032_, 1, v_k_1882_);
lean_ctor_set(v_reuseFailAlloc_2032_, 2, v_v_1883_);
lean_ctor_set(v_reuseFailAlloc_2032_, 3, v_l_1888_);
lean_ctor_set(v_reuseFailAlloc_2032_, 4, v_r_1889_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
else
{
lean_object* v_impl_2033_; lean_object* v___x_2034_; 
lean_dec(v_size_1885_);
v_impl_2033_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_k_1882_, v_v_1883_, v_l_1888_);
v___x_2034_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1889_) == 0)
{
lean_object* v_size_2035_; lean_object* v_size_2036_; lean_object* v_k_2037_; lean_object* v_v_2038_; lean_object* v_l_2039_; lean_object* v_r_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; uint8_t v___x_2043_; 
v_size_2035_ = lean_ctor_get(v_r_1889_, 0);
v_size_2036_ = lean_ctor_get(v_impl_2033_, 0);
lean_inc(v_size_2036_);
v_k_2037_ = lean_ctor_get(v_impl_2033_, 1);
lean_inc(v_k_2037_);
v_v_2038_ = lean_ctor_get(v_impl_2033_, 2);
lean_inc(v_v_2038_);
v_l_2039_ = lean_ctor_get(v_impl_2033_, 3);
lean_inc(v_l_2039_);
v_r_2040_ = lean_ctor_get(v_impl_2033_, 4);
lean_inc(v_r_2040_);
v___x_2041_ = lean_unsigned_to_nat(3u);
v___x_2042_ = lean_nat_mul(v___x_2041_, v_size_2035_);
v___x_2043_ = lean_nat_dec_lt(v___x_2042_, v_size_2036_);
lean_dec(v___x_2042_);
if (v___x_2043_ == 0)
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2047_; 
lean_dec(v_r_2040_);
lean_dec(v_l_2039_);
lean_dec(v_v_2038_);
lean_dec(v_k_2037_);
v___x_2044_ = lean_nat_add(v___x_2034_, v_size_2036_);
lean_dec(v_size_2036_);
v___x_2045_ = lean_nat_add(v___x_2044_, v_size_2035_);
lean_dec(v___x_2044_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 3, v_impl_2033_);
lean_ctor_set(v___x_1891_, 0, v___x_2045_);
v___x_2047_ = v___x_1891_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2045_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v_k_1886_);
lean_ctor_set(v_reuseFailAlloc_2048_, 2, v_v_1887_);
lean_ctor_set(v_reuseFailAlloc_2048_, 3, v_impl_2033_);
lean_ctor_set(v_reuseFailAlloc_2048_, 4, v_r_1889_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
else
{
lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2114_; 
v_isSharedCheck_2114_ = !lean_is_exclusive(v_impl_2033_);
if (v_isSharedCheck_2114_ == 0)
{
lean_object* v_unused_2115_; lean_object* v_unused_2116_; lean_object* v_unused_2117_; lean_object* v_unused_2118_; lean_object* v_unused_2119_; 
v_unused_2115_ = lean_ctor_get(v_impl_2033_, 4);
lean_dec(v_unused_2115_);
v_unused_2116_ = lean_ctor_get(v_impl_2033_, 3);
lean_dec(v_unused_2116_);
v_unused_2117_ = lean_ctor_get(v_impl_2033_, 2);
lean_dec(v_unused_2117_);
v_unused_2118_ = lean_ctor_get(v_impl_2033_, 1);
lean_dec(v_unused_2118_);
v_unused_2119_ = lean_ctor_get(v_impl_2033_, 0);
lean_dec(v_unused_2119_);
v___x_2050_ = v_impl_2033_;
v_isShared_2051_ = v_isSharedCheck_2114_;
goto v_resetjp_2049_;
}
else
{
lean_dec(v_impl_2033_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2114_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v_size_2052_; lean_object* v_size_2053_; lean_object* v_k_2054_; lean_object* v_v_2055_; lean_object* v_l_2056_; lean_object* v_r_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; uint8_t v___x_2060_; 
v_size_2052_ = lean_ctor_get(v_l_2039_, 0);
v_size_2053_ = lean_ctor_get(v_r_2040_, 0);
v_k_2054_ = lean_ctor_get(v_r_2040_, 1);
v_v_2055_ = lean_ctor_get(v_r_2040_, 2);
v_l_2056_ = lean_ctor_get(v_r_2040_, 3);
v_r_2057_ = lean_ctor_get(v_r_2040_, 4);
v___x_2058_ = lean_unsigned_to_nat(2u);
v___x_2059_ = lean_nat_mul(v___x_2058_, v_size_2052_);
v___x_2060_ = lean_nat_dec_lt(v_size_2053_, v___x_2059_);
lean_dec(v___x_2059_);
if (v___x_2060_ == 0)
{
lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2089_; 
lean_inc(v_r_2057_);
lean_inc(v_l_2056_);
lean_inc(v_v_2055_);
lean_inc(v_k_2054_);
v_isSharedCheck_2089_ = !lean_is_exclusive(v_r_2040_);
if (v_isSharedCheck_2089_ == 0)
{
lean_object* v_unused_2090_; lean_object* v_unused_2091_; lean_object* v_unused_2092_; lean_object* v_unused_2093_; lean_object* v_unused_2094_; 
v_unused_2090_ = lean_ctor_get(v_r_2040_, 4);
lean_dec(v_unused_2090_);
v_unused_2091_ = lean_ctor_get(v_r_2040_, 3);
lean_dec(v_unused_2091_);
v_unused_2092_ = lean_ctor_get(v_r_2040_, 2);
lean_dec(v_unused_2092_);
v_unused_2093_ = lean_ctor_get(v_r_2040_, 1);
lean_dec(v_unused_2093_);
v_unused_2094_ = lean_ctor_get(v_r_2040_, 0);
lean_dec(v_unused_2094_);
v___x_2062_ = v_r_2040_;
v_isShared_2063_ = v_isSharedCheck_2089_;
goto v_resetjp_2061_;
}
else
{
lean_dec(v_r_2040_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2089_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v___x_2077_; lean_object* v___y_2079_; 
v___x_2064_ = lean_nat_add(v___x_2034_, v_size_2036_);
lean_dec(v_size_2036_);
v___x_2065_ = lean_nat_add(v___x_2064_, v_size_2035_);
lean_dec(v___x_2064_);
v___x_2077_ = lean_nat_add(v___x_2034_, v_size_2052_);
if (lean_obj_tag(v_l_2056_) == 0)
{
lean_object* v_size_2087_; 
v_size_2087_ = lean_ctor_get(v_l_2056_, 0);
lean_inc(v_size_2087_);
v___y_2079_ = v_size_2087_;
goto v___jp_2078_;
}
else
{
lean_object* v___x_2088_; 
v___x_2088_ = lean_unsigned_to_nat(0u);
v___y_2079_ = v___x_2088_;
goto v___jp_2078_;
}
v___jp_2066_:
{
lean_object* v___x_2070_; lean_object* v___x_2072_; 
v___x_2070_ = lean_nat_add(v___y_2067_, v___y_2069_);
lean_dec(v___y_2069_);
lean_dec(v___y_2067_);
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 4, v_r_1889_);
lean_ctor_set(v___x_2062_, 3, v_r_2057_);
lean_ctor_set(v___x_2062_, 2, v_v_1887_);
lean_ctor_set(v___x_2062_, 1, v_k_1886_);
lean_ctor_set(v___x_2062_, 0, v___x_2070_);
v___x_2072_ = v___x_2062_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2070_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v_k_1886_);
lean_ctor_set(v_reuseFailAlloc_2076_, 2, v_v_1887_);
lean_ctor_set(v_reuseFailAlloc_2076_, 3, v_r_2057_);
lean_ctor_set(v_reuseFailAlloc_2076_, 4, v_r_1889_);
v___x_2072_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
lean_object* v___x_2074_; 
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 4, v___x_2072_);
lean_ctor_set(v___x_2050_, 3, v___y_2068_);
lean_ctor_set(v___x_2050_, 2, v_v_2055_);
lean_ctor_set(v___x_2050_, 1, v_k_2054_);
lean_ctor_set(v___x_2050_, 0, v___x_2065_);
v___x_2074_ = v___x_2050_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2065_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v_k_2054_);
lean_ctor_set(v_reuseFailAlloc_2075_, 2, v_v_2055_);
lean_ctor_set(v_reuseFailAlloc_2075_, 3, v___y_2068_);
lean_ctor_set(v_reuseFailAlloc_2075_, 4, v___x_2072_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
v___jp_2078_:
{
lean_object* v___x_2080_; lean_object* v___x_2082_; 
v___x_2080_ = lean_nat_add(v___x_2077_, v___y_2079_);
lean_dec(v___y_2079_);
lean_dec(v___x_2077_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 4, v_l_2056_);
lean_ctor_set(v___x_1891_, 3, v_l_2039_);
lean_ctor_set(v___x_1891_, 2, v_v_2038_);
lean_ctor_set(v___x_1891_, 1, v_k_2037_);
lean_ctor_set(v___x_1891_, 0, v___x_2080_);
v___x_2082_ = v___x_1891_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2080_);
lean_ctor_set(v_reuseFailAlloc_2086_, 1, v_k_2037_);
lean_ctor_set(v_reuseFailAlloc_2086_, 2, v_v_2038_);
lean_ctor_set(v_reuseFailAlloc_2086_, 3, v_l_2039_);
lean_ctor_set(v_reuseFailAlloc_2086_, 4, v_l_2056_);
v___x_2082_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
lean_object* v___x_2083_; 
v___x_2083_ = lean_nat_add(v___x_2034_, v_size_2035_);
if (lean_obj_tag(v_r_2057_) == 0)
{
lean_object* v_size_2084_; 
v_size_2084_ = lean_ctor_get(v_r_2057_, 0);
lean_inc(v_size_2084_);
v___y_2067_ = v___x_2083_;
v___y_2068_ = v___x_2082_;
v___y_2069_ = v_size_2084_;
goto v___jp_2066_;
}
else
{
lean_object* v___x_2085_; 
v___x_2085_ = lean_unsigned_to_nat(0u);
v___y_2067_ = v___x_2083_;
v___y_2068_ = v___x_2082_;
v___y_2069_ = v___x_2085_;
goto v___jp_2066_;
}
}
}
}
}
else
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2100_; 
lean_del_object(v___x_1891_);
v___x_2095_ = lean_nat_add(v___x_2034_, v_size_2036_);
lean_dec(v_size_2036_);
v___x_2096_ = lean_nat_add(v___x_2095_, v_size_2035_);
lean_dec(v___x_2095_);
v___x_2097_ = lean_nat_add(v___x_2034_, v_size_2035_);
v___x_2098_ = lean_nat_add(v___x_2097_, v_size_2053_);
lean_dec(v___x_2097_);
lean_inc_ref(v_r_1889_);
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 4, v_r_1889_);
lean_ctor_set(v___x_2050_, 3, v_r_2040_);
lean_ctor_set(v___x_2050_, 2, v_v_1887_);
lean_ctor_set(v___x_2050_, 1, v_k_1886_);
lean_ctor_set(v___x_2050_, 0, v___x_2098_);
v___x_2100_ = v___x_2050_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2098_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v_k_1886_);
lean_ctor_set(v_reuseFailAlloc_2113_, 2, v_v_1887_);
lean_ctor_set(v_reuseFailAlloc_2113_, 3, v_r_2040_);
lean_ctor_set(v_reuseFailAlloc_2113_, 4, v_r_1889_);
v___x_2100_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
v_isSharedCheck_2107_ = !lean_is_exclusive(v_r_1889_);
if (v_isSharedCheck_2107_ == 0)
{
lean_object* v_unused_2108_; lean_object* v_unused_2109_; lean_object* v_unused_2110_; lean_object* v_unused_2111_; lean_object* v_unused_2112_; 
v_unused_2108_ = lean_ctor_get(v_r_1889_, 4);
lean_dec(v_unused_2108_);
v_unused_2109_ = lean_ctor_get(v_r_1889_, 3);
lean_dec(v_unused_2109_);
v_unused_2110_ = lean_ctor_get(v_r_1889_, 2);
lean_dec(v_unused_2110_);
v_unused_2111_ = lean_ctor_get(v_r_1889_, 1);
lean_dec(v_unused_2111_);
v_unused_2112_ = lean_ctor_get(v_r_1889_, 0);
lean_dec(v_unused_2112_);
v___x_2102_ = v_r_1889_;
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
else
{
lean_dec(v_r_1889_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 4, v___x_2100_);
lean_ctor_set(v___x_2102_, 3, v_l_2039_);
lean_ctor_set(v___x_2102_, 2, v_v_2038_);
lean_ctor_set(v___x_2102_, 1, v_k_2037_);
lean_ctor_set(v___x_2102_, 0, v___x_2096_);
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2096_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v_k_2037_);
lean_ctor_set(v_reuseFailAlloc_2106_, 2, v_v_2038_);
lean_ctor_set(v_reuseFailAlloc_2106_, 3, v_l_2039_);
lean_ctor_set(v_reuseFailAlloc_2106_, 4, v___x_2100_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2120_; 
v_l_2120_ = lean_ctor_get(v_impl_2033_, 3);
lean_inc(v_l_2120_);
if (lean_obj_tag(v_l_2120_) == 0)
{
lean_object* v_r_2121_; lean_object* v_k_2122_; lean_object* v_v_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2134_; 
v_r_2121_ = lean_ctor_get(v_impl_2033_, 4);
v_k_2122_ = lean_ctor_get(v_impl_2033_, 1);
v_v_2123_ = lean_ctor_get(v_impl_2033_, 2);
v_isSharedCheck_2134_ = !lean_is_exclusive(v_impl_2033_);
if (v_isSharedCheck_2134_ == 0)
{
lean_object* v_unused_2135_; lean_object* v_unused_2136_; 
v_unused_2135_ = lean_ctor_get(v_impl_2033_, 3);
lean_dec(v_unused_2135_);
v_unused_2136_ = lean_ctor_get(v_impl_2033_, 0);
lean_dec(v_unused_2136_);
v___x_2125_ = v_impl_2033_;
v_isShared_2126_ = v_isSharedCheck_2134_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_r_2121_);
lean_inc(v_v_2123_);
lean_inc(v_k_2122_);
lean_dec(v_impl_2033_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2134_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v___x_2127_; lean_object* v___x_2129_; 
v___x_2127_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2121_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 3, v_r_2121_);
lean_ctor_set(v___x_2125_, 2, v_v_1887_);
lean_ctor_set(v___x_2125_, 1, v_k_1886_);
lean_ctor_set(v___x_2125_, 0, v___x_2034_);
v___x_2129_ = v___x_2125_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v___x_2034_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_k_1886_);
lean_ctor_set(v_reuseFailAlloc_2133_, 2, v_v_1887_);
lean_ctor_set(v_reuseFailAlloc_2133_, 3, v_r_2121_);
lean_ctor_set(v_reuseFailAlloc_2133_, 4, v_r_2121_);
v___x_2129_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
lean_object* v___x_2131_; 
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 4, v___x_2129_);
lean_ctor_set(v___x_1891_, 3, v_l_2120_);
lean_ctor_set(v___x_1891_, 2, v_v_2123_);
lean_ctor_set(v___x_1891_, 1, v_k_2122_);
lean_ctor_set(v___x_1891_, 0, v___x_2127_);
v___x_2131_ = v___x_1891_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2127_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v_k_2122_);
lean_ctor_set(v_reuseFailAlloc_2132_, 2, v_v_2123_);
lean_ctor_set(v_reuseFailAlloc_2132_, 3, v_l_2120_);
lean_ctor_set(v_reuseFailAlloc_2132_, 4, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
else
{
lean_object* v_r_2137_; 
v_r_2137_ = lean_ctor_get(v_impl_2033_, 4);
lean_inc(v_r_2137_);
if (lean_obj_tag(v_r_2137_) == 0)
{
lean_object* v_k_2138_; lean_object* v_v_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2162_; 
v_k_2138_ = lean_ctor_get(v_impl_2033_, 1);
v_v_2139_ = lean_ctor_get(v_impl_2033_, 2);
v_isSharedCheck_2162_ = !lean_is_exclusive(v_impl_2033_);
if (v_isSharedCheck_2162_ == 0)
{
lean_object* v_unused_2163_; lean_object* v_unused_2164_; lean_object* v_unused_2165_; 
v_unused_2163_ = lean_ctor_get(v_impl_2033_, 4);
lean_dec(v_unused_2163_);
v_unused_2164_ = lean_ctor_get(v_impl_2033_, 3);
lean_dec(v_unused_2164_);
v_unused_2165_ = lean_ctor_get(v_impl_2033_, 0);
lean_dec(v_unused_2165_);
v___x_2141_ = v_impl_2033_;
v_isShared_2142_ = v_isSharedCheck_2162_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_v_2139_);
lean_inc(v_k_2138_);
lean_dec(v_impl_2033_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2162_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v_k_2143_; lean_object* v_v_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2158_; 
v_k_2143_ = lean_ctor_get(v_r_2137_, 1);
v_v_2144_ = lean_ctor_get(v_r_2137_, 2);
v_isSharedCheck_2158_ = !lean_is_exclusive(v_r_2137_);
if (v_isSharedCheck_2158_ == 0)
{
lean_object* v_unused_2159_; lean_object* v_unused_2160_; lean_object* v_unused_2161_; 
v_unused_2159_ = lean_ctor_get(v_r_2137_, 4);
lean_dec(v_unused_2159_);
v_unused_2160_ = lean_ctor_get(v_r_2137_, 3);
lean_dec(v_unused_2160_);
v_unused_2161_ = lean_ctor_get(v_r_2137_, 0);
lean_dec(v_unused_2161_);
v___x_2146_ = v_r_2137_;
v_isShared_2147_ = v_isSharedCheck_2158_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_v_2144_);
lean_inc(v_k_2143_);
lean_dec(v_r_2137_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2158_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2148_; lean_object* v___x_2150_; 
v___x_2148_ = lean_unsigned_to_nat(3u);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 4, v_l_2120_);
lean_ctor_set(v___x_2146_, 3, v_l_2120_);
lean_ctor_set(v___x_2146_, 2, v_v_2139_);
lean_ctor_set(v___x_2146_, 1, v_k_2138_);
lean_ctor_set(v___x_2146_, 0, v___x_2034_);
v___x_2150_ = v___x_2146_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v___x_2034_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v_k_2138_);
lean_ctor_set(v_reuseFailAlloc_2157_, 2, v_v_2139_);
lean_ctor_set(v_reuseFailAlloc_2157_, 3, v_l_2120_);
lean_ctor_set(v_reuseFailAlloc_2157_, 4, v_l_2120_);
v___x_2150_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
lean_object* v___x_2152_; 
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 4, v_l_2120_);
lean_ctor_set(v___x_2141_, 2, v_v_1887_);
lean_ctor_set(v___x_2141_, 1, v_k_1886_);
lean_ctor_set(v___x_2141_, 0, v___x_2034_);
v___x_2152_ = v___x_2141_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2034_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_k_1886_);
lean_ctor_set(v_reuseFailAlloc_2156_, 2, v_v_1887_);
lean_ctor_set(v_reuseFailAlloc_2156_, 3, v_l_2120_);
lean_ctor_set(v_reuseFailAlloc_2156_, 4, v_l_2120_);
v___x_2152_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2154_; 
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 4, v___x_2152_);
lean_ctor_set(v___x_1891_, 3, v___x_2150_);
lean_ctor_set(v___x_1891_, 2, v_v_2144_);
lean_ctor_set(v___x_1891_, 1, v_k_2143_);
lean_ctor_set(v___x_1891_, 0, v___x_2148_);
v___x_2154_ = v___x_1891_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2148_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_k_2143_);
lean_ctor_set(v_reuseFailAlloc_2155_, 2, v_v_2144_);
lean_ctor_set(v_reuseFailAlloc_2155_, 3, v___x_2150_);
lean_ctor_set(v_reuseFailAlloc_2155_, 4, v___x_2152_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
}
}
else
{
lean_object* v___x_2166_; lean_object* v___x_2168_; 
v___x_2166_ = lean_unsigned_to_nat(2u);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 4, v_r_2137_);
lean_ctor_set(v___x_1891_, 3, v_impl_2033_);
lean_ctor_set(v___x_1891_, 0, v___x_2166_);
v___x_2168_ = v___x_1891_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2166_);
lean_ctor_set(v_reuseFailAlloc_2169_, 1, v_k_1886_);
lean_ctor_set(v_reuseFailAlloc_2169_, 2, v_v_1887_);
lean_ctor_set(v_reuseFailAlloc_2169_, 3, v_impl_2033_);
lean_ctor_set(v_reuseFailAlloc_2169_, 4, v_r_2137_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = lean_unsigned_to_nat(1u);
v___x_2172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
lean_ctor_set(v___x_2172_, 1, v_k_1882_);
lean_ctor_set(v___x_2172_, 2, v_v_1883_);
lean_ctor_set(v___x_2172_, 3, v_t_1884_);
lean_ctor_set(v___x_2172_, 4, v_t_1884_);
return v___x_2172_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(lean_object* v_as_x27_2173_, lean_object* v_b_2174_){
_start:
{
if (lean_obj_tag(v_as_x27_2173_) == 0)
{
return v_b_2174_;
}
else
{
lean_object* v_head_2175_; lean_object* v_tail_2176_; lean_object* v_fst_2177_; lean_object* v_snd_2178_; lean_object* v_r_2179_; 
v_head_2175_ = lean_ctor_get(v_as_x27_2173_, 0);
lean_inc(v_head_2175_);
v_tail_2176_ = lean_ctor_get(v_as_x27_2173_, 1);
lean_inc(v_tail_2176_);
lean_dec_ref(v_as_x27_2173_);
v_fst_2177_ = lean_ctor_get(v_head_2175_, 0);
lean_inc(v_fst_2177_);
v_snd_2178_ = lean_ctor_get(v_head_2175_, 1);
lean_inc(v_snd_2178_);
lean_dec(v_head_2175_);
v_r_2179_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_fst_2177_, v_snd_2178_, v_b_2174_);
v_as_x27_2173_ = v_tail_2176_;
v_b_2174_ = v_r_2179_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(lean_object* v_firsts_2181_, lean_object* v_n_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v___y_2187_; lean_object* v___y_2188_; lean_object* v___y_2219_; lean_object* v_val_2220_; lean_object* v___x_2222_; lean_object* v___y_2224_; lean_object* v_env_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2222_ = lean_st_ref_get(v___y_2184_);
v_env_2239_ = lean_ctor_get(v___x_2222_, 0);
lean_inc_ref(v_env_2239_);
lean_dec(v___x_2222_);
v___x_2240_ = l_Lean_Environment_constants(v_env_2239_);
v___x_2241_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___redArg(v___x_2240_, v_n_2182_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v___x_2242_; 
v___x_2242_ = lean_box(0);
v___y_2224_ = v___x_2242_;
goto v___jp_2223_;
}
else
{
lean_object* v_val_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v_val_2243_ = lean_ctor_get(v___x_2241_, 0);
lean_inc(v_val_2243_);
lean_dec_ref(v___x_2241_);
v___x_2244_ = l_Lean_ConstantInfo_levelParams(v_val_2243_);
lean_dec(v_val_2243_);
v___x_2245_ = lean_box(0);
v___x_2246_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__14(v___x_2244_, v___x_2245_);
v___y_2224_ = v___x_2246_;
goto v___jp_2223_;
}
v___jp_2186_:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; uint8_t v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; uint8_t v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v_r_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2189_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__0));
v___x_2190_ = lean_unsigned_to_nat(0u);
v___x_2191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
lean_ctor_set(v___x_2191_, 1, v___y_2188_);
v___x_2192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2189_);
lean_ctor_set(v___x_2192_, 1, v___x_2191_);
v___x_2193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2192_);
lean_ctor_set(v___x_2193_, 1, v___x_2189_);
v___x_2194_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__2));
v___x_2195_ = lean_box(2);
v___x_2196_ = 1;
lean_inc(v_n_2182_);
v___x_2197_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_2182_, v___x_2196_);
v___x_2198_ = lean_string_utf8_byte_size(v___x_2197_);
v___x_2199_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2197_);
lean_ctor_set(v___x_2199_, 1, v___x_2190_);
lean_ctor_set(v___x_2199_, 2, v___x_2198_);
v___x_2200_ = lean_box(0);
lean_inc(v_n_2182_);
v___x_2201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2201_, 0, v_n_2182_);
lean_ctor_set(v___x_2201_, 1, v___x_2200_);
v___x_2202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
lean_ctor_set(v___x_2202_, 1, v___x_2200_);
lean_inc(v_n_2182_);
v___x_2203_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2195_);
lean_ctor_set(v___x_2203_, 1, v___x_2199_);
lean_ctor_set(v___x_2203_, 2, v_n_2182_);
lean_ctor_set(v___x_2203_, 3, v___x_2202_);
v___x_2204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2194_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
v___x_2205_ = l_Lean_LocalContext_empty;
v___x_2206_ = lean_box(0);
v___x_2207_ = l_Lean_Expr_const___override(v_n_2182_, v___y_2187_);
v___x_2208_ = 0;
v___x_2209_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2209_, 0, v___x_2204_);
lean_ctor_set(v___x_2209_, 1, v___x_2205_);
lean_ctor_set(v___x_2209_, 2, v___x_2206_);
lean_ctor_set(v___x_2209_, 3, v___x_2207_);
lean_ctor_set_uint8(v___x_2209_, sizeof(void*)*4, v___x_2208_);
lean_ctor_set_uint8(v___x_2209_, sizeof(void*)*4 + 1, v___x_2208_);
v___x_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
v___x_2211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2190_);
lean_ctor_set(v___x_2211_, 1, v___x_2210_);
v___x_2212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
lean_ctor_set(v___x_2212_, 1, v___x_2200_);
v_r_2213_ = lean_box(1);
v___x_2214_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v___x_2212_, v_r_2213_);
v___x_2215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2193_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
v___x_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
v___x_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2216_);
return v___x_2217_;
}
v___jp_2218_:
{
lean_object* v___x_2221_; 
v___x_2221_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2221_, 0, v_val_2220_);
v___y_2187_ = v___y_2219_;
v___y_2188_ = v___x_2221_;
goto v___jp_2186_;
}
v___jp_2223_:
{
lean_object* v___x_2225_; lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2238_; 
lean_inc(v_n_2182_);
v___x_2225_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_n_2182_, v___y_2184_);
v_a_2226_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2228_ = v___x_2225_;
v_isShared_2229_ = v_isSharedCheck_2238_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2225_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2238_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
if (lean_obj_tag(v_a_2226_) == 0)
{
lean_object* v___x_2230_; 
v___x_2230_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg(v_firsts_2181_, v_n_2182_);
if (lean_obj_tag(v___x_2230_) == 0)
{
uint8_t v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2234_; 
v___x_2231_ = 1;
lean_inc(v_n_2182_);
v___x_2232_ = l_Lean_Name_toString(v_n_2182_, v___x_2231_);
if (v_isShared_2229_ == 0)
{
lean_ctor_set_tag(v___x_2228_, 3);
lean_ctor_set(v___x_2228_, 0, v___x_2232_);
v___x_2234_ = v___x_2228_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2232_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
v___y_2187_ = v___y_2224_;
v___y_2188_ = v___x_2234_;
goto v___jp_2186_;
}
}
else
{
lean_object* v_val_2236_; 
lean_del_object(v___x_2228_);
v_val_2236_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_val_2236_);
lean_dec_ref(v___x_2230_);
v___y_2219_ = v___y_2224_;
v_val_2220_ = v_val_2236_;
goto v___jp_2218_;
}
}
else
{
lean_object* v_val_2237_; 
lean_del_object(v___x_2228_);
v_val_2237_ = lean_ctor_get(v_a_2226_, 0);
lean_inc(v_val_2237_);
lean_dec_ref(v_a_2226_);
v___y_2219_ = v___y_2224_;
v_val_2220_ = v_val_2237_;
goto v___jp_2218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6___boxed(lean_object* v_firsts_2247_, lean_object* v_n_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_firsts_2247_, v_n_2248_, v___y_2249_, v___y_2250_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v_firsts_2247_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(lean_object* v_a_2253_, lean_object* v_x_2254_, lean_object* v_x_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
if (lean_obj_tag(v_x_2254_) == 0)
{
lean_object* v___x_2259_; lean_object* v___x_2260_; 
v___x_2259_ = l_List_reverse___redArg(v_x_2255_);
v___x_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2259_);
return v___x_2260_;
}
else
{
lean_object* v_head_2261_; lean_object* v_tail_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2280_; 
v_head_2261_ = lean_ctor_get(v_x_2254_, 0);
v_tail_2262_ = lean_ctor_get(v_x_2254_, 1);
v_isSharedCheck_2280_ = !lean_is_exclusive(v_x_2254_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2264_ = v_x_2254_;
v_isShared_2265_ = v_isSharedCheck_2280_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_tail_2262_);
lean_inc(v_head_2261_);
lean_dec(v_x_2254_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2280_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; 
v___x_2266_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_a_2253_, v_head_2261_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; lean_object* v___x_2269_; 
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_a_2267_);
lean_dec_ref(v___x_2266_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 1, v_x_2255_);
lean_ctor_set(v___x_2264_, 0, v_a_2267_);
v___x_2269_ = v___x_2264_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_a_2267_);
lean_ctor_set(v_reuseFailAlloc_2271_, 1, v_x_2255_);
v___x_2269_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
v_x_2254_ = v_tail_2262_;
v_x_2255_ = v___x_2269_;
goto _start;
}
}
else
{
lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
lean_del_object(v___x_2264_);
lean_dec(v_tail_2262_);
lean_dec(v_x_2255_);
v_a_2272_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2266_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2266_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7___boxed(lean_object* v_a_2281_, lean_object* v_x_2282_, lean_object* v_x_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_2281_, v_x_2282_, v_x_2283_, v___y_2284_, v___y_2285_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v_a_2281_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(lean_object* v_val_2288_, lean_object* v___x_2289_, lean_object* v___x_2290_, lean_object* v_a_2291_, lean_object* v_b_2292_){
_start:
{
lean_object* v_it_2294_; lean_object* v_startInclusive_2295_; lean_object* v_endExclusive_2296_; 
if (lean_obj_tag(v_a_2291_) == 0)
{
lean_object* v_currPos_2301_; lean_object* v_searcher_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2328_; 
v_currPos_2301_ = lean_ctor_get(v_a_2291_, 0);
v_searcher_2302_ = lean_ctor_get(v_a_2291_, 1);
v_isSharedCheck_2328_ = !lean_is_exclusive(v_a_2291_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2304_ = v_a_2291_;
v_isShared_2305_ = v_isSharedCheck_2328_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_searcher_2302_);
lean_inc(v_currPos_2301_);
lean_dec(v_a_2291_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2328_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v_startInclusive_2306_; lean_object* v_endExclusive_2307_; lean_object* v___x_2308_; uint8_t v___x_2309_; 
v_startInclusive_2306_ = lean_ctor_get(v___x_2289_, 1);
v_endExclusive_2307_ = lean_ctor_get(v___x_2289_, 2);
v___x_2308_ = lean_nat_sub(v_endExclusive_2307_, v_startInclusive_2306_);
v___x_2309_ = lean_nat_dec_eq(v_searcher_2302_, v___x_2308_);
lean_dec(v___x_2308_);
if (v___x_2309_ == 0)
{
uint32_t v___x_2310_; uint32_t v___x_2311_; uint8_t v___x_2312_; 
v___x_2310_ = 10;
v___x_2311_ = lean_string_utf8_get_fast(v_val_2288_, v_searcher_2302_);
v___x_2312_ = lean_uint32_dec_eq(v___x_2311_, v___x_2310_);
if (v___x_2312_ == 0)
{
lean_object* v___x_2313_; lean_object* v___x_2315_; 
v___x_2313_ = lean_string_utf8_next_fast(v_val_2288_, v_searcher_2302_);
lean_dec(v_searcher_2302_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 1, v___x_2313_);
v___x_2315_ = v___x_2304_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_currPos_2301_);
lean_ctor_set(v_reuseFailAlloc_2317_, 1, v___x_2313_);
v___x_2315_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
v_a_2291_ = v___x_2315_;
goto _start;
}
}
else
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v_slice_2321_; lean_object* v_nextIt_2323_; 
v___x_2318_ = lean_string_utf8_next_fast(v_val_2288_, v_searcher_2302_);
v___x_2319_ = lean_nat_sub(v___x_2318_, v_searcher_2302_);
v___x_2320_ = lean_nat_add(v_searcher_2302_, v___x_2319_);
lean_dec(v___x_2319_);
v_slice_2321_ = l_String_Slice_subslice_x21(v___x_2289_, v_currPos_2301_, v_searcher_2302_);
lean_inc(v___x_2320_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 1, v___x_2320_);
lean_ctor_set(v___x_2304_, 0, v___x_2320_);
v_nextIt_2323_ = v___x_2304_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2320_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v___x_2320_);
v_nextIt_2323_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
lean_object* v_startInclusive_2324_; lean_object* v_endExclusive_2325_; 
v_startInclusive_2324_ = lean_ctor_get(v_slice_2321_, 0);
lean_inc(v_startInclusive_2324_);
v_endExclusive_2325_ = lean_ctor_get(v_slice_2321_, 1);
lean_inc(v_endExclusive_2325_);
lean_dec_ref(v_slice_2321_);
v_it_2294_ = v_nextIt_2323_;
v_startInclusive_2295_ = v_startInclusive_2324_;
v_endExclusive_2296_ = v_endExclusive_2325_;
goto v___jp_2293_;
}
}
}
else
{
lean_object* v___x_2327_; 
lean_del_object(v___x_2304_);
lean_dec(v_searcher_2302_);
v___x_2327_ = lean_box(1);
lean_inc(v___x_2290_);
v_it_2294_ = v___x_2327_;
v_startInclusive_2295_ = v_currPos_2301_;
v_endExclusive_2296_ = v___x_2290_;
goto v___jp_2293_;
}
}
}
else
{
lean_dec(v___x_2290_);
return v_b_2292_;
}
v___jp_2293_:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2297_ = lean_string_utf8_extract(v_val_2288_, v_startInclusive_2295_, v_endExclusive_2296_);
lean_dec(v_endExclusive_2296_);
lean_dec(v_startInclusive_2295_);
v___x_2298_ = l_Lean_stringToMessageData(v___x_2297_);
v___x_2299_ = lean_array_push(v_b_2292_, v___x_2298_);
v_a_2291_ = v_it_2294_;
v_b_2292_ = v___x_2299_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg___boxed(lean_object* v_val_2329_, lean_object* v___x_2330_, lean_object* v___x_2331_, lean_object* v_a_2332_, lean_object* v_b_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2329_, v___x_2330_, v___x_2331_, v_a_2332_, v_b_2333_);
lean_dec_ref(v___x_2330_);
lean_dec_ref(v_val_2329_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__17(lean_object* v_init_2335_, lean_object* v_x_2336_){
_start:
{
if (lean_obj_tag(v_x_2336_) == 0)
{
lean_object* v_k_2337_; lean_object* v_l_2338_; lean_object* v_r_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v_k_2337_ = lean_ctor_get(v_x_2336_, 1);
lean_inc(v_k_2337_);
v_l_2338_ = lean_ctor_get(v_x_2336_, 3);
lean_inc(v_l_2338_);
v_r_2339_ = lean_ctor_get(v_x_2336_, 4);
lean_inc(v_r_2339_);
lean_dec_ref(v_x_2336_);
v___x_2340_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__17(v_init_2335_, v_l_2338_);
v___x_2341_ = lean_array_push(v___x_2340_, v_k_2337_);
v_init_2335_ = v___x_2341_;
v_x_2336_ = v_r_2339_;
goto _start;
}
else
{
return v_init_2335_;
}
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2(void){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1));
v___x_2347_ = l_Lean_stringToMessageData(v___x_2346_);
return v___x_2347_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4(void){
_start:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2349_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3));
v___x_2350_ = l_Lean_stringToMessageData(v___x_2349_);
return v___x_2350_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6(void){
_start:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2352_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5));
v___x_2353_ = l_Lean_stringToMessageData(v___x_2352_);
return v___x_2353_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9(void){
_start:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2357_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8));
v___x_2358_ = l_Lean_MessageData_ofFormat(v___x_2357_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_x_2361_, lean_object* v_x_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
if (lean_obj_tag(v_x_2361_) == 0)
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2366_ = l_List_reverse___redArg(v_x_2362_);
v___x_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
return v___x_2367_;
}
else
{
lean_object* v_head_2368_; lean_object* v_tail_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2466_; 
v_head_2368_ = lean_ctor_get(v_x_2361_, 0);
v_tail_2369_ = lean_ctor_get(v_x_2361_, 1);
v_isSharedCheck_2466_ = !lean_is_exclusive(v_x_2361_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2371_ = v_x_2361_;
v_isShared_2372_ = v_isSharedCheck_2466_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_tail_2369_);
lean_inc(v_head_2368_);
lean_dec(v_x_2361_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2466_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___y_2374_; lean_object* v___y_2375_; lean_object* v___y_2376_; lean_object* v___y_2377_; lean_object* v_snd_2386_; lean_object* v_fst_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2465_; 
v_snd_2386_ = lean_ctor_get(v_head_2368_, 1);
v_fst_2387_ = lean_ctor_get(v_head_2368_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v_head_2368_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2389_ = v_head_2368_;
v_isShared_2390_ = v_isSharedCheck_2465_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_snd_2386_);
lean_inc(v_fst_2387_);
lean_dec(v_head_2368_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2465_;
goto v_resetjp_2388_;
}
v___jp_2373_:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2383_; 
v___x_2378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2378_, 0, v___y_2376_);
lean_ctor_set(v___x_2378_, 1, v___y_2377_);
v___x_2379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2378_);
lean_ctor_set(v___x_2379_, 1, v___y_2374_);
v___x_2380_ = l_Lean_MessageData_nestD(v___x_2379_);
v___x_2381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2381_, 0, v___y_2375_);
lean_ctor_set(v___x_2381_, 1, v___x_2380_);
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 1, v_x_2362_);
lean_ctor_set(v___x_2371_, 0, v___x_2381_);
v___x_2383_ = v___x_2371_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2381_);
lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_x_2362_);
v___x_2383_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
v_x_2361_ = v_tail_2369_;
v_x_2362_ = v___x_2383_;
goto _start;
}
}
v_resetjp_2388_:
{
lean_object* v_fst_2391_; lean_object* v_snd_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2464_; 
v_fst_2391_ = lean_ctor_get(v_snd_2386_, 0);
v_snd_2392_ = lean_ctor_get(v_snd_2386_, 1);
v_isSharedCheck_2464_ = !lean_is_exclusive(v_snd_2386_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2394_ = v_snd_2386_;
v_isShared_2395_ = v_isSharedCheck_2464_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_snd_2392_);
lean_inc(v_fst_2391_);
lean_dec(v_snd_2386_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2464_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v_a_2419_; lean_object* v___y_2435_; lean_object* v___x_2444_; 
v___x_2444_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_2360_, v_fst_2387_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_object* v___x_2445_; 
v___x_2445_ = l_Lean_MessageData_nil;
v_a_2419_ = v___x_2445_;
goto v___jp_2418_;
}
else
{
lean_object* v_val_2446_; 
v_val_2446_ = lean_ctor_get(v___x_2444_, 0);
lean_inc(v_val_2446_);
lean_dec_ref(v___x_2444_);
if (lean_obj_tag(v_val_2446_) == 0)
{
lean_object* v_size_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___x_2454_; lean_object* v___x_2455_; uint8_t v___x_2456_; 
v_size_2447_ = lean_ctor_get(v_val_2446_, 0);
v___x_2448_ = lean_mk_empty_array_with_capacity(v_size_2447_);
v___x_2449_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__17(v___x_2448_, v_val_2446_);
v___x_2454_ = lean_array_get_size(v___x_2449_);
v___x_2455_ = lean_unsigned_to_nat(0u);
v___x_2456_ = lean_nat_dec_eq(v___x_2454_, v___x_2455_);
if (v___x_2456_ == 0)
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___y_2460_; uint8_t v___x_2462_; 
v___x_2457_ = lean_unsigned_to_nat(1u);
v___x_2458_ = lean_nat_sub(v___x_2454_, v___x_2457_);
v___x_2462_ = lean_nat_dec_le(v___x_2455_, v___x_2458_);
if (v___x_2462_ == 0)
{
lean_inc(v___x_2458_);
v___y_2460_ = v___x_2458_;
goto v___jp_2459_;
}
else
{
v___y_2460_ = v___x_2455_;
goto v___jp_2459_;
}
v___jp_2459_:
{
uint8_t v___x_2461_; 
v___x_2461_ = lean_nat_dec_le(v___y_2460_, v___x_2458_);
if (v___x_2461_ == 0)
{
lean_dec(v___x_2458_);
lean_inc(v___y_2460_);
v___y_2451_ = v___y_2460_;
v___y_2452_ = v___y_2460_;
goto v___jp_2450_;
}
else
{
v___y_2451_ = v___y_2460_;
v___y_2452_ = v___x_2458_;
goto v___jp_2450_;
}
}
}
else
{
v___y_2435_ = v___x_2449_;
goto v___jp_2434_;
}
v___jp_2450_:
{
lean_object* v___x_2453_; 
v___x_2453_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v___x_2449_, v___y_2451_, v___y_2452_);
lean_dec(v___y_2452_);
v___y_2435_ = v___x_2453_;
goto v___jp_2434_;
}
}
else
{
lean_object* v___x_2463_; 
v___x_2463_ = l_Lean_MessageData_nil;
v_a_2419_ = v___x_2463_;
goto v___jp_2418_;
}
}
v___jp_2396_:
{
lean_object* v___x_2402_; 
if (v_isShared_2395_ == 0)
{
lean_ctor_set_tag(v___x_2394_, 7);
lean_ctor_set(v___x_2394_, 1, v___y_2400_);
lean_ctor_set(v___x_2394_, 0, v___y_2399_);
v___x_2402_ = v___x_2394_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___y_2399_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v___y_2400_);
v___x_2402_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
if (lean_obj_tag(v_snd_2392_) == 0)
{
lean_object* v___x_2403_; 
lean_del_object(v___x_2389_);
v___x_2403_ = l_Lean_MessageData_nil;
v___y_2374_ = v___y_2397_;
v___y_2375_ = v___y_2398_;
v___y_2376_ = v___x_2402_;
v___y_2377_ = v___x_2403_;
goto v___jp_2373_;
}
else
{
lean_object* v_val_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2415_; 
v_val_2404_ = lean_ctor_get(v_snd_2392_, 0);
lean_inc(v_val_2404_);
lean_dec_ref(v_snd_2392_);
v___x_2405_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2406_ = lean_unsigned_to_nat(0u);
v___x_2407_ = lean_string_utf8_byte_size(v_val_2404_);
lean_inc(v_val_2404_);
v___x_2408_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2408_, 0, v_val_2404_);
lean_ctor_set(v___x_2408_, 1, v___x_2406_);
lean_ctor_set(v___x_2408_, 2, v___x_2407_);
v___x_2409_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v___x_2408_);
v___x_2410_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0));
v___x_2411_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2404_, v___x_2408_, v___x_2407_, v___x_2409_, v___x_2410_);
lean_dec_ref(v___x_2408_);
lean_dec(v_val_2404_);
v___x_2412_ = lean_array_to_list(v___x_2411_);
v___x_2413_ = l_Lean_MessageData_joinSep(v___x_2412_, v___x_2405_);
if (v_isShared_2390_ == 0)
{
lean_ctor_set_tag(v___x_2389_, 7);
lean_ctor_set(v___x_2389_, 1, v___x_2413_);
lean_ctor_set(v___x_2389_, 0, v___x_2405_);
v___x_2415_ = v___x_2389_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2405_);
lean_ctor_set(v_reuseFailAlloc_2416_, 1, v___x_2413_);
v___x_2415_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
v___y_2374_ = v___y_2397_;
v___y_2375_ = v___y_2398_;
v___y_2376_ = v___x_2402_;
v___y_2377_ = v___x_2415_;
goto v___jp_2373_;
}
}
}
}
v___jp_2418_:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; uint8_t v___x_2425_; lean_object* v___x_2426_; uint8_t v___x_2427_; 
v___x_2420_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2);
v___x_2421_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
lean_inc(v_fst_2387_);
v___x_2422_ = l_Lean_MessageData_ofName(v_fst_2387_);
v___x_2423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2421_);
lean_ctor_set(v___x_2423_, 1, v___x_2422_);
v___x_2424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
lean_ctor_set(v___x_2424_, 1, v___x_2421_);
v___x_2425_ = 1;
v___x_2426_ = l_Lean_Name_toString(v_fst_2387_, v___x_2425_);
v___x_2427_ = lean_string_dec_eq(v___x_2426_, v_fst_2391_);
lean_dec_ref(v___x_2426_);
if (v___x_2427_ == 0)
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2428_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4);
v___x_2429_ = l_Lean_stringToMessageData(v_fst_2391_);
v___x_2430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2428_);
lean_ctor_set(v___x_2430_, 1, v___x_2429_);
v___x_2431_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6);
v___x_2432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2432_, 0, v___x_2430_);
lean_ctor_set(v___x_2432_, 1, v___x_2431_);
v___y_2397_ = v_a_2419_;
v___y_2398_ = v___x_2420_;
v___y_2399_ = v___x_2424_;
v___y_2400_ = v___x_2432_;
goto v___jp_2396_;
}
else
{
lean_object* v___x_2433_; 
lean_dec(v_fst_2391_);
v___x_2433_ = l_Lean_MessageData_nil;
v___y_2397_ = v_a_2419_;
v___y_2398_ = v___x_2420_;
v___y_2399_ = v___x_2424_;
v___y_2400_ = v___x_2433_;
goto v___jp_2396_;
}
}
v___jp_2434_:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2436_ = lean_array_to_list(v___y_2435_);
v___x_2437_ = lean_box(0);
v___x_2438_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_2359_, v___x_2436_, v___x_2437_, v___y_2363_, v___y_2364_);
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_object* v_a_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v_a_2439_ = lean_ctor_get(v___x_2438_, 0);
lean_inc(v_a_2439_);
lean_dec_ref(v___x_2438_);
v___x_2440_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2441_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9);
v___x_2442_ = l_Lean_MessageData_joinSep(v_a_2439_, v___x_2441_);
v___x_2443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2440_);
lean_ctor_set(v___x_2443_, 1, v___x_2442_);
v_a_2419_ = v___x_2443_;
goto v___jp_2418_;
}
else
{
lean_del_object(v___x_2394_);
lean_dec(v_snd_2392_);
lean_dec(v_fst_2391_);
lean_del_object(v___x_2389_);
lean_dec(v_fst_2387_);
lean_del_object(v___x_2371_);
lean_dec(v_tail_2369_);
lean_dec(v_x_2362_);
return v___x_2438_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___boxed(lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_x_2469_, lean_object* v_x_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_2467_, v_a_2468_, v_x_2469_, v_x_2470_, v___y_2471_, v___y_2472_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v_a_2468_);
lean_dec(v_a_2467_);
return v_res_2474_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32___lam__0(uint8_t v___y_2476_, uint8_t v_suppressElabErrors_2477_, lean_object* v_x_2478_){
_start:
{
if (lean_obj_tag(v_x_2478_) == 1)
{
lean_object* v_pre_2479_; 
v_pre_2479_ = lean_ctor_get(v_x_2478_, 0);
if (lean_obj_tag(v_pre_2479_) == 0)
{
lean_object* v_str_2480_; lean_object* v___x_2481_; uint8_t v___x_2482_; 
v_str_2480_ = lean_ctor_get(v_x_2478_, 1);
v___x_2481_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32___lam__0___closed__0));
v___x_2482_ = lean_string_dec_eq(v_str_2480_, v___x_2481_);
if (v___x_2482_ == 0)
{
return v___y_2476_;
}
else
{
return v_suppressElabErrors_2477_;
}
}
else
{
return v___y_2476_;
}
}
else
{
return v___y_2476_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32___lam__0___boxed(lean_object* v___y_2483_, lean_object* v_suppressElabErrors_2484_, lean_object* v_x_2485_){
_start:
{
uint8_t v___y_20100__boxed_2486_; uint8_t v_suppressElabErrors_boxed_2487_; uint8_t v_res_2488_; lean_object* v_r_2489_; 
v___y_20100__boxed_2486_ = lean_unbox(v___y_2483_);
v_suppressElabErrors_boxed_2487_ = lean_unbox(v_suppressElabErrors_2484_);
v_res_2488_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32___lam__0(v___y_20100__boxed_2486_, v_suppressElabErrors_boxed_2487_, v_x_2485_);
lean_dec(v_x_2485_);
v_r_2489_ = lean_box(v_res_2488_);
return v_r_2489_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32(lean_object* v_ref_2490_, lean_object* v_msgData_2491_, uint8_t v_severity_2492_, uint8_t v_isSilent_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
uint8_t v___y_2498_; uint8_t v___y_2499_; lean_object* v___y_2500_; lean_object* v___y_2501_; lean_object* v___y_2502_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; uint8_t v___y_2561_; uint8_t v___y_2562_; uint8_t v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2565_; uint8_t v___y_2589_; uint8_t v___y_2590_; lean_object* v___y_2591_; uint8_t v___y_2592_; lean_object* v___y_2593_; uint8_t v___y_2597_; uint8_t v___y_2598_; uint8_t v___y_2599_; uint8_t v___x_2614_; uint8_t v___y_2616_; uint8_t v___y_2617_; uint8_t v___y_2618_; uint8_t v___y_2620_; uint8_t v___x_2632_; 
v___x_2614_ = 2;
v___x_2632_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2492_, v___x_2614_);
if (v___x_2632_ == 0)
{
v___y_2620_ = v___x_2632_;
goto v___jp_2619_;
}
else
{
uint8_t v___x_2633_; 
lean_inc_ref(v_msgData_2491_);
v___x_2633_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2491_);
v___y_2620_ = v___x_2633_;
goto v___jp_2619_;
}
v___jp_2497_:
{
lean_object* v___x_2506_; 
v___x_2506_ = l_Lean_Elab_Command_getScope___redArg(v___y_2505_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v_a_2507_; lean_object* v___x_2508_; 
v_a_2507_ = lean_ctor_get(v___x_2506_, 0);
lean_inc(v_a_2507_);
lean_dec_ref(v___x_2506_);
v___x_2508_ = l_Lean_Elab_Command_getScope___redArg(v___y_2505_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2543_; 
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2511_ = v___x_2508_;
v_isShared_2512_ = v_isSharedCheck_2543_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2508_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2543_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2513_; lean_object* v_currNamespace_2514_; lean_object* v_openDecls_2515_; lean_object* v_env_2516_; lean_object* v_messages_2517_; lean_object* v_scopes_2518_; lean_object* v_usedQuotCtxts_2519_; lean_object* v_nextMacroScope_2520_; lean_object* v_maxRecDepth_2521_; lean_object* v_ngen_2522_; lean_object* v_auxDeclNGen_2523_; lean_object* v_infoState_2524_; lean_object* v_traceState_2525_; lean_object* v_snapshotTasks_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2542_; 
v___x_2513_ = lean_st_ref_take(v___y_2505_);
v_currNamespace_2514_ = lean_ctor_get(v_a_2507_, 2);
lean_inc(v_currNamespace_2514_);
lean_dec(v_a_2507_);
v_openDecls_2515_ = lean_ctor_get(v_a_2509_, 3);
lean_inc(v_openDecls_2515_);
lean_dec(v_a_2509_);
v_env_2516_ = lean_ctor_get(v___x_2513_, 0);
v_messages_2517_ = lean_ctor_get(v___x_2513_, 1);
v_scopes_2518_ = lean_ctor_get(v___x_2513_, 2);
v_usedQuotCtxts_2519_ = lean_ctor_get(v___x_2513_, 3);
v_nextMacroScope_2520_ = lean_ctor_get(v___x_2513_, 4);
v_maxRecDepth_2521_ = lean_ctor_get(v___x_2513_, 5);
v_ngen_2522_ = lean_ctor_get(v___x_2513_, 6);
v_auxDeclNGen_2523_ = lean_ctor_get(v___x_2513_, 7);
v_infoState_2524_ = lean_ctor_get(v___x_2513_, 8);
v_traceState_2525_ = lean_ctor_get(v___x_2513_, 9);
v_snapshotTasks_2526_ = lean_ctor_get(v___x_2513_, 10);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2528_ = v___x_2513_;
v_isShared_2529_ = v_isSharedCheck_2542_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_snapshotTasks_2526_);
lean_inc(v_traceState_2525_);
lean_inc(v_infoState_2524_);
lean_inc(v_auxDeclNGen_2523_);
lean_inc(v_ngen_2522_);
lean_inc(v_maxRecDepth_2521_);
lean_inc(v_nextMacroScope_2520_);
lean_inc(v_usedQuotCtxts_2519_);
lean_inc(v_scopes_2518_);
lean_inc(v_messages_2517_);
lean_inc(v_env_2516_);
lean_dec(v___x_2513_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2542_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2535_; 
v___x_2530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2530_, 0, v_currNamespace_2514_);
lean_ctor_set(v___x_2530_, 1, v_openDecls_2515_);
v___x_2531_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2530_);
lean_ctor_set(v___x_2531_, 1, v___y_2500_);
v___x_2532_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2532_, 0, v___y_2502_);
lean_ctor_set(v___x_2532_, 1, v___y_2501_);
lean_ctor_set(v___x_2532_, 2, v___y_2503_);
lean_ctor_set(v___x_2532_, 3, v___y_2504_);
lean_ctor_set(v___x_2532_, 4, v___x_2531_);
lean_ctor_set_uint8(v___x_2532_, sizeof(void*)*5, v___y_2498_);
lean_ctor_set_uint8(v___x_2532_, sizeof(void*)*5 + 1, v___y_2499_);
lean_ctor_set_uint8(v___x_2532_, sizeof(void*)*5 + 2, v_isSilent_2493_);
v___x_2533_ = l_Lean_MessageLog_add(v___x_2532_, v_messages_2517_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 1, v___x_2533_);
v___x_2535_ = v___x_2528_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_env_2516_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v___x_2533_);
lean_ctor_set(v_reuseFailAlloc_2541_, 2, v_scopes_2518_);
lean_ctor_set(v_reuseFailAlloc_2541_, 3, v_usedQuotCtxts_2519_);
lean_ctor_set(v_reuseFailAlloc_2541_, 4, v_nextMacroScope_2520_);
lean_ctor_set(v_reuseFailAlloc_2541_, 5, v_maxRecDepth_2521_);
lean_ctor_set(v_reuseFailAlloc_2541_, 6, v_ngen_2522_);
lean_ctor_set(v_reuseFailAlloc_2541_, 7, v_auxDeclNGen_2523_);
lean_ctor_set(v_reuseFailAlloc_2541_, 8, v_infoState_2524_);
lean_ctor_set(v_reuseFailAlloc_2541_, 9, v_traceState_2525_);
lean_ctor_set(v_reuseFailAlloc_2541_, 10, v_snapshotTasks_2526_);
v___x_2535_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2539_; 
v___x_2536_ = lean_st_ref_set(v___y_2505_, v___x_2535_);
v___x_2537_ = lean_box(0);
if (v_isShared_2512_ == 0)
{
lean_ctor_set(v___x_2511_, 0, v___x_2537_);
v___x_2539_ = v___x_2511_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2537_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
lean_dec(v_a_2507_);
lean_dec_ref(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec_ref(v___y_2500_);
v_a_2544_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2508_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2508_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
else
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2559_; 
lean_dec_ref(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec_ref(v___y_2500_);
v_a_2552_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2554_ = v___x_2506_;
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2506_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2557_; 
if (v_isShared_2555_ == 0)
{
v___x_2557_ = v___x_2554_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2552_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
}
v___jp_2560_:
{
lean_object* v_fileName_2566_; lean_object* v_fileMap_2567_; uint8_t v_suppressElabErrors_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v_a_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2587_; 
v_fileName_2566_ = lean_ctor_get(v___y_2494_, 0);
lean_inc_ref(v_fileName_2566_);
v_fileMap_2567_ = lean_ctor_get(v___y_2494_, 1);
lean_inc_ref(v_fileMap_2567_);
v_suppressElabErrors_2568_ = lean_ctor_get_uint8(v___y_2494_, sizeof(void*)*10);
lean_dec_ref(v___y_2494_);
v___x_2569_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2491_);
v___x_2570_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v___x_2569_, v___y_2495_);
v_a_2571_ = lean_ctor_get(v___x_2570_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2573_ = v___x_2570_;
v_isShared_2574_ = v_isSharedCheck_2587_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_a_2571_);
lean_dec(v___x_2570_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2587_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
lean_inc_ref(v_fileMap_2567_);
v___x_2575_ = l_Lean_FileMap_toPosition(v_fileMap_2567_, v___y_2564_);
lean_dec(v___y_2564_);
v___x_2576_ = l_Lean_FileMap_toPosition(v_fileMap_2567_, v___y_2565_);
lean_dec(v___y_2565_);
v___x_2577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2576_);
v___x_2578_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0));
if (v_suppressElabErrors_2568_ == 0)
{
lean_del_object(v___x_2573_);
v___y_2498_ = v___y_2562_;
v___y_2499_ = v___y_2563_;
v___y_2500_ = v_a_2571_;
v___y_2501_ = v___x_2575_;
v___y_2502_ = v_fileName_2566_;
v___y_2503_ = v___x_2577_;
v___y_2504_ = v___x_2578_;
v___y_2505_ = v___y_2495_;
goto v___jp_2497_;
}
else
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___f_2581_; uint8_t v___x_2582_; 
v___x_2579_ = lean_box(v___y_2561_);
v___x_2580_ = lean_box(v_suppressElabErrors_2568_);
v___f_2581_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2581_, 0, v___x_2579_);
lean_closure_set(v___f_2581_, 1, v___x_2580_);
lean_inc(v_a_2571_);
v___x_2582_ = l_Lean_MessageData_hasTag(v___f_2581_, v_a_2571_);
if (v___x_2582_ == 0)
{
lean_object* v___x_2583_; lean_object* v___x_2585_; 
lean_dec_ref(v___x_2577_);
lean_dec_ref(v___x_2575_);
lean_dec(v_a_2571_);
lean_dec_ref(v_fileName_2566_);
v___x_2583_ = lean_box(0);
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 0, v___x_2583_);
v___x_2585_ = v___x_2573_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2583_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
else
{
lean_del_object(v___x_2573_);
v___y_2498_ = v___y_2562_;
v___y_2499_ = v___y_2563_;
v___y_2500_ = v_a_2571_;
v___y_2501_ = v___x_2575_;
v___y_2502_ = v_fileName_2566_;
v___y_2503_ = v___x_2577_;
v___y_2504_ = v___x_2578_;
v___y_2505_ = v___y_2495_;
goto v___jp_2497_;
}
}
}
}
v___jp_2588_:
{
lean_object* v___x_2594_; 
v___x_2594_ = l_Lean_Syntax_getTailPos_x3f(v___y_2591_, v___y_2590_);
lean_dec(v___y_2591_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_inc(v___y_2593_);
v___y_2561_ = v___y_2589_;
v___y_2562_ = v___y_2590_;
v___y_2563_ = v___y_2592_;
v___y_2564_ = v___y_2593_;
v___y_2565_ = v___y_2593_;
goto v___jp_2560_;
}
else
{
lean_object* v_val_2595_; 
v_val_2595_ = lean_ctor_get(v___x_2594_, 0);
lean_inc(v_val_2595_);
lean_dec_ref(v___x_2594_);
v___y_2561_ = v___y_2589_;
v___y_2562_ = v___y_2590_;
v___y_2563_ = v___y_2592_;
v___y_2564_ = v___y_2593_;
v___y_2565_ = v_val_2595_;
goto v___jp_2560_;
}
}
v___jp_2596_:
{
lean_object* v___x_2600_; 
v___x_2600_ = l_Lean_Elab_Command_getRef___redArg(v___y_2494_);
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; lean_object* v_ref_2602_; lean_object* v___x_2603_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_a_2601_);
lean_dec_ref(v___x_2600_);
v_ref_2602_ = l_Lean_replaceRef(v_ref_2490_, v_a_2601_);
lean_dec(v_a_2601_);
v___x_2603_ = l_Lean_Syntax_getPos_x3f(v_ref_2602_, v___y_2598_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v___x_2604_; 
v___x_2604_ = lean_unsigned_to_nat(0u);
v___y_2589_ = v___y_2597_;
v___y_2590_ = v___y_2598_;
v___y_2591_ = v_ref_2602_;
v___y_2592_ = v___y_2599_;
v___y_2593_ = v___x_2604_;
goto v___jp_2588_;
}
else
{
lean_object* v_val_2605_; 
v_val_2605_ = lean_ctor_get(v___x_2603_, 0);
lean_inc(v_val_2605_);
lean_dec_ref(v___x_2603_);
v___y_2589_ = v___y_2597_;
v___y_2590_ = v___y_2598_;
v___y_2591_ = v_ref_2602_;
v___y_2592_ = v___y_2599_;
v___y_2593_ = v_val_2605_;
goto v___jp_2588_;
}
}
else
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
lean_dec_ref(v___y_2494_);
lean_dec_ref(v_msgData_2491_);
v_a_2606_ = lean_ctor_get(v___x_2600_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2600_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2600_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2600_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
v___jp_2615_:
{
if (v___y_2618_ == 0)
{
v___y_2597_ = v___y_2616_;
v___y_2598_ = v___y_2617_;
v___y_2599_ = v_severity_2492_;
goto v___jp_2596_;
}
else
{
v___y_2597_ = v___y_2616_;
v___y_2598_ = v___y_2617_;
v___y_2599_ = v___x_2614_;
goto v___jp_2596_;
}
}
v___jp_2619_:
{
if (v___y_2620_ == 0)
{
lean_object* v___x_2621_; lean_object* v_scopes_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v_opts_2625_; uint8_t v___x_2626_; uint8_t v___x_2627_; 
v___x_2621_ = lean_st_ref_get(v___y_2495_);
v_scopes_2622_ = lean_ctor_get(v___x_2621_, 2);
lean_inc(v_scopes_2622_);
lean_dec(v___x_2621_);
v___x_2623_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2624_ = l_List_head_x21___redArg(v___x_2623_, v_scopes_2622_);
lean_dec(v_scopes_2622_);
v_opts_2625_ = lean_ctor_get(v___x_2624_, 1);
lean_inc_ref(v_opts_2625_);
lean_dec(v___x_2624_);
v___x_2626_ = 1;
v___x_2627_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2492_, v___x_2626_);
if (v___x_2627_ == 0)
{
lean_dec_ref(v_opts_2625_);
v___y_2616_ = v___y_2620_;
v___y_2617_ = v___y_2620_;
v___y_2618_ = v___x_2627_;
goto v___jp_2615_;
}
else
{
lean_object* v___x_2628_; uint8_t v___x_2629_; 
v___x_2628_ = l_Lean_warningAsError;
v___x_2629_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(v_opts_2625_, v___x_2628_);
lean_dec_ref(v_opts_2625_);
v___y_2616_ = v___y_2620_;
v___y_2617_ = v___y_2620_;
v___y_2618_ = v___x_2629_;
goto v___jp_2615_;
}
}
else
{
lean_object* v___x_2630_; lean_object* v___x_2631_; 
lean_dec_ref(v___y_2494_);
lean_dec_ref(v_msgData_2491_);
v___x_2630_ = lean_box(0);
v___x_2631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2630_);
return v___x_2631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32___boxed(lean_object* v_ref_2634_, lean_object* v_msgData_2635_, lean_object* v_severity_2636_, lean_object* v_isSilent_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
uint8_t v_severity_boxed_2641_; uint8_t v_isSilent_boxed_2642_; lean_object* v_res_2643_; 
v_severity_boxed_2641_ = lean_unbox(v_severity_2636_);
v_isSilent_boxed_2642_ = lean_unbox(v_isSilent_2637_);
v_res_2643_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32(v_ref_2634_, v_msgData_2635_, v_severity_boxed_2641_, v_isSilent_boxed_2642_, v___y_2638_, v___y_2639_);
lean_dec(v___y_2639_);
lean_dec(v_ref_2634_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27(lean_object* v_msgData_2644_, uint8_t v_severity_2645_, uint8_t v_isSilent_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v___x_2650_; 
v___x_2650_ = l_Lean_Elab_Command_getRef___redArg(v___y_2647_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; lean_object* v___x_2652_; 
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2651_);
lean_dec_ref(v___x_2650_);
v___x_2652_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27_spec__32(v_a_2651_, v_msgData_2644_, v_severity_2645_, v_isSilent_2646_, v___y_2647_, v___y_2648_);
lean_dec(v_a_2651_);
return v___x_2652_;
}
else
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2660_; 
lean_dec_ref(v___y_2647_);
lean_dec_ref(v_msgData_2644_);
v_a_2653_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2655_ = v___x_2650_;
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2650_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2658_; 
if (v_isShared_2656_ == 0)
{
v___x_2658_ = v___x_2655_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_a_2653_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27___boxed(lean_object* v_msgData_2661_, lean_object* v_severity_2662_, lean_object* v_isSilent_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
uint8_t v_severity_boxed_2667_; uint8_t v_isSilent_boxed_2668_; lean_object* v_res_2669_; 
v_severity_boxed_2667_ = lean_unbox(v_severity_2662_);
v_isSilent_boxed_2668_ = lean_unbox(v_isSilent_2663_);
v_res_2669_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27(v_msgData_2661_, v_severity_boxed_2667_, v_isSilent_boxed_2668_, v___y_2664_, v___y_2665_);
lean_dec(v___y_2665_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(lean_object* v_msgData_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
uint8_t v___x_2674_; uint8_t v___x_2675_; lean_object* v___x_2676_; 
v___x_2674_ = 0;
v___x_2675_ = 0;
v___x_2676_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__27(v_msgData_2670_, v___x_2674_, v___x_2675_, v___y_2671_, v___y_2672_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12___boxed(lean_object* v_msgData_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v_res_2681_; 
v_res_2681_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v_msgData_2677_, v___y_2678_, v___y_2679_);
lean_dec(v___y_2679_);
return v_res_2681_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__26(lean_object* v_init_2682_, lean_object* v_x_2683_){
_start:
{
if (lean_obj_tag(v_x_2683_) == 0)
{
lean_object* v_k_2684_; lean_object* v_v_2685_; lean_object* v_l_2686_; lean_object* v_r_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v_k_2684_ = lean_ctor_get(v_x_2683_, 1);
v_v_2685_ = lean_ctor_get(v_x_2683_, 2);
v_l_2686_ = lean_ctor_get(v_x_2683_, 3);
v_r_2687_ = lean_ctor_get(v_x_2683_, 4);
v___x_2688_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__26(v_init_2682_, v_l_2686_);
lean_inc(v_v_2685_);
lean_inc(v_k_2684_);
v___x_2689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2689_, 0, v_k_2684_);
lean_ctor_set(v___x_2689_, 1, v_v_2685_);
v___x_2690_ = lean_array_push(v___x_2688_, v___x_2689_);
v_init_2682_ = v___x_2690_;
v_x_2683_ = v_r_2687_;
goto _start;
}
else
{
return v_init_2682_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__26___boxed(lean_object* v_init_2692_, lean_object* v_x_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__26(v_init_2692_, v_x_2693_);
lean_dec(v_x_2693_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___redArg(lean_object* v_as_2695_, size_t v_sz_2696_, size_t v_i_2697_, lean_object* v_b_2698_){
_start:
{
uint8_t v___x_2700_; 
v___x_2700_ = lean_usize_dec_lt(v_i_2697_, v_sz_2696_);
if (v___x_2700_ == 0)
{
lean_object* v___x_2701_; 
v___x_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2701_, 0, v_b_2698_);
return v___x_2701_;
}
else
{
lean_object* v_a_2702_; lean_object* v_fst_2703_; lean_object* v_snd_2704_; lean_object* v_found_2705_; size_t v___x_2706_; size_t v___x_2707_; 
v_a_2702_ = lean_array_uget_borrowed(v_as_2695_, v_i_2697_);
v_fst_2703_ = lean_ctor_get(v_a_2702_, 0);
v_snd_2704_ = lean_ctor_get(v_a_2702_, 1);
lean_inc(v_snd_2704_);
lean_inc(v_fst_2703_);
v_found_2705_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2703_, v_snd_2704_, v_b_2698_);
v___x_2706_ = ((size_t)1ULL);
v___x_2707_ = lean_usize_add(v_i_2697_, v___x_2706_);
v_i_2697_ = v___x_2707_;
v_b_2698_ = v_found_2705_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___redArg___boxed(lean_object* v_as_2709_, lean_object* v_sz_2710_, lean_object* v_i_2711_, lean_object* v_b_2712_, lean_object* v___y_2713_){
_start:
{
size_t v_sz_boxed_2714_; size_t v_i_boxed_2715_; lean_object* v_res_2716_; 
v_sz_boxed_2714_ = lean_unbox_usize(v_sz_2710_);
lean_dec(v_sz_2710_);
v_i_boxed_2715_ = lean_unbox_usize(v_i_2711_);
lean_dec(v_i_2711_);
v_res_2716_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___redArg(v_as_2709_, v_sz_boxed_2714_, v_i_boxed_2715_, v_b_2712_);
lean_dec_ref(v_as_2709_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(lean_object* v_as_2717_, size_t v_sz_2718_, size_t v_i_2719_, lean_object* v_b_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
uint8_t v___x_2724_; 
v___x_2724_ = lean_usize_dec_lt(v_i_2719_, v_sz_2718_);
if (v___x_2724_ == 0)
{
lean_object* v___x_2725_; 
v___x_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2725_, 0, v_b_2720_);
return v___x_2725_;
}
else
{
lean_object* v_a_2726_; size_t v_sz_2727_; size_t v___x_2728_; lean_object* v___x_2729_; 
v_a_2726_ = lean_array_uget_borrowed(v_as_2717_, v_i_2719_);
v_sz_2727_ = lean_array_size(v_a_2726_);
v___x_2728_ = ((size_t)0ULL);
v___x_2729_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___redArg(v_a_2726_, v_sz_2727_, v___x_2728_, v_b_2720_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v_a_2730_; size_t v___x_2731_; size_t v___x_2732_; 
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_a_2730_);
lean_dec_ref(v___x_2729_);
v___x_2731_ = ((size_t)1ULL);
v___x_2732_ = lean_usize_add(v_i_2719_, v___x_2731_);
v_i_2719_ = v___x_2732_;
v_b_2720_ = v_a_2730_;
goto _start;
}
else
{
return v___x_2729_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___boxed(lean_object* v_as_2734_, lean_object* v_sz_2735_, lean_object* v_i_2736_, lean_object* v_b_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
size_t v_sz_boxed_2741_; size_t v_i_boxed_2742_; lean_object* v_res_2743_; 
v_sz_boxed_2741_ = lean_unbox_usize(v_sz_2735_);
lean_dec(v_sz_2735_);
v_i_boxed_2742_ = lean_unbox_usize(v_i_2736_);
lean_dec(v_i_2736_);
v_res_2743_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(v_as_2734_, v_sz_boxed_2741_, v_i_boxed_2742_, v_b_2737_, v___y_2738_, v___y_2739_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec_ref(v_as_2734_);
return v_res_2743_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___lam__0(uint8_t v___x_2744_, lean_object* v_x1_2745_, lean_object* v_x2_2746_){
_start:
{
lean_object* v_fst_2747_; lean_object* v_fst_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; uint8_t v___x_2751_; 
v_fst_2747_ = lean_ctor_get(v_x1_2745_, 0);
lean_inc(v_fst_2747_);
lean_dec_ref(v_x1_2745_);
v_fst_2748_ = lean_ctor_get(v_x2_2746_, 0);
lean_inc(v_fst_2748_);
lean_dec_ref(v_x2_2746_);
v___x_2749_ = l_Lean_Name_toString(v_fst_2747_, v___x_2744_);
v___x_2750_ = l_Lean_Name_toString(v_fst_2748_, v___x_2744_);
v___x_2751_ = lean_string_dec_lt(v___x_2749_, v___x_2750_);
lean_dec_ref(v___x_2750_);
lean_dec_ref(v___x_2749_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___lam__0___boxed(lean_object* v___x_2752_, lean_object* v_x1_2753_, lean_object* v_x2_2754_){
_start:
{
uint8_t v___x_20475__boxed_2755_; uint8_t v_res_2756_; lean_object* v_r_2757_; 
v___x_20475__boxed_2755_ = lean_unbox(v___x_2752_);
v_res_2756_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___lam__0(v___x_20475__boxed_2755_, v_x1_2753_, v_x2_2754_);
v_r_2757_ = lean_box(v_res_2756_);
return v_r_2757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(lean_object* v_as_2758_, lean_object* v_lo_2759_, lean_object* v_hi_2760_){
_start:
{
uint8_t v___x_2761_; 
v___x_2761_ = lean_nat_dec_lt(v_lo_2759_, v_hi_2760_);
if (v___x_2761_ == 0)
{
lean_dec(v_lo_2759_);
return v_as_2758_;
}
else
{
lean_object* v___x_2762_; lean_object* v___f_2763_; lean_object* v___x_2764_; lean_object* v_fst_2765_; lean_object* v_snd_2766_; uint8_t v___x_2767_; 
v___x_2762_ = lean_box(v___x_2761_);
v___f_2763_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2763_, 0, v___x_2762_);
lean_inc(v_lo_2759_);
v___x_2764_ = l_Array_qpartition___redArg(v_as_2758_, v___f_2763_, v_lo_2759_, v_hi_2760_);
v_fst_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_fst_2765_);
v_snd_2766_ = lean_ctor_get(v___x_2764_, 1);
lean_inc(v_snd_2766_);
lean_dec_ref(v___x_2764_);
v___x_2767_ = lean_nat_dec_le(v_hi_2760_, v_fst_2765_);
if (v___x_2767_ == 0)
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2768_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_snd_2766_, v_lo_2759_, v_fst_2765_);
v___x_2769_ = lean_unsigned_to_nat(1u);
v___x_2770_ = lean_nat_add(v_fst_2765_, v___x_2769_);
lean_dec(v_fst_2765_);
v_as_2758_ = v___x_2768_;
v_lo_2759_ = v___x_2770_;
goto _start;
}
else
{
lean_dec(v_fst_2765_);
lean_dec(v_lo_2759_);
return v_snd_2766_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg___boxed(lean_object* v_as_2772_, lean_object* v_lo_2773_, lean_object* v_hi_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_as_2772_, v_lo_2773_, v_hi_2774_);
lean_dec(v_hi_2774_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg(lean_object* v_init_2776_, lean_object* v_x_2777_){
_start:
{
if (lean_obj_tag(v_x_2777_) == 0)
{
lean_object* v_k_2779_; lean_object* v_v_2780_; lean_object* v_l_2781_; lean_object* v_r_2782_; lean_object* v___x_2783_; lean_object* v_a_2784_; lean_object* v_a_2785_; lean_object* v___x_2786_; 
v_k_2779_ = lean_ctor_get(v_x_2777_, 1);
lean_inc(v_k_2779_);
v_v_2780_ = lean_ctor_get(v_x_2777_, 2);
lean_inc(v_v_2780_);
v_l_2781_ = lean_ctor_get(v_x_2777_, 3);
lean_inc(v_l_2781_);
v_r_2782_ = lean_ctor_get(v_x_2777_, 4);
lean_inc(v_r_2782_);
lean_dec_ref(v_x_2777_);
v___x_2783_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg(v_init_2776_, v_l_2781_);
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
lean_inc(v_a_2784_);
lean_dec_ref(v___x_2783_);
v_a_2785_ = lean_ctor_get(v_a_2784_, 0);
lean_inc(v_a_2785_);
lean_dec(v_a_2784_);
v___x_2786_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2779_, v_v_2780_, v_a_2785_);
v_init_2776_ = v___x_2786_;
v_x_2777_ = v_r_2782_;
goto _start;
}
else
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2788_, 0, v_init_2776_);
v___x_2789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2788_);
return v___x_2789_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg___boxed(lean_object* v_init_2790_, lean_object* v_x_2791_, lean_object* v___y_2792_){
_start:
{
lean_object* v_res_2793_; 
v_res_2793_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg(v_init_2790_, v_x_2791_);
return v_res_2793_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2794_ = lean_box(1);
v___x_2795_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2794_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
lean_object* v___y_2802_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___x_2817_; lean_object* v_env_2818_; lean_object* v___x_2819_; lean_object* v_toEnvExtension_2820_; lean_object* v_asyncMode_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v_a_2827_; lean_object* v_a_2829_; lean_object* v_a_2852_; 
v___x_2817_ = lean_st_ref_get(v___y_2799_);
v_env_2818_ = lean_ctor_get(v___x_2817_, 0);
lean_inc_ref(v_env_2818_);
lean_dec(v___x_2817_);
v___x_2819_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc_ref(v_toEnvExtension_2820_);
v_asyncMode_2821_ = lean_ctor_get(v_toEnvExtension_2820_, 2);
lean_inc(v_asyncMode_2821_);
v___x_2822_ = lean_box(1);
v___x_2823_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0, &l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0_once, _init_l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0);
v___x_2824_ = lean_box(0);
lean_inc_ref(v_env_2818_);
v___x_2825_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2822_, v___x_2819_, v_env_2818_, v_asyncMode_2821_, v___x_2824_);
v___x_2826_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg(v___x_2822_, v___x_2825_);
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_a_2827_);
lean_dec_ref(v___x_2826_);
v_a_2852_ = lean_ctor_get(v_a_2827_, 0);
lean_inc(v_a_2852_);
lean_dec(v_a_2827_);
v_a_2829_ = v_a_2852_;
goto v___jp_2828_;
v___jp_2801_:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2803_ = lean_array_to_list(v___y_2802_);
v___x_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2803_);
return v___x_2804_;
}
v___jp_2805_:
{
lean_object* v___x_2810_; 
lean_dec(v___y_2808_);
v___x_2810_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v___y_2807_, v___y_2806_, v___y_2809_);
lean_dec(v___y_2809_);
v___y_2802_ = v___x_2810_;
goto v___jp_2801_;
}
v___jp_2811_:
{
uint8_t v___x_2816_; 
v___x_2816_ = lean_nat_dec_le(v___y_2815_, v___y_2813_);
if (v___x_2816_ == 0)
{
lean_dec(v___y_2813_);
lean_inc(v___y_2815_);
v___y_2806_ = v___y_2815_;
v___y_2807_ = v___y_2812_;
v___y_2808_ = v___y_2814_;
v___y_2809_ = v___y_2815_;
goto v___jp_2805_;
}
else
{
v___y_2806_ = v___y_2815_;
v___y_2807_ = v___y_2812_;
v___y_2808_ = v___y_2814_;
v___y_2809_ = v___y_2813_;
goto v___jp_2805_;
}
}
v___jp_2828_:
{
lean_object* v___x_2830_; lean_object* v_importedEntries_2831_; size_t v_sz_2832_; size_t v___x_2833_; lean_object* v___x_2834_; 
v___x_2830_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2823_, v_toEnvExtension_2820_, v_env_2818_, v_asyncMode_2821_, v___x_2824_);
lean_dec(v_asyncMode_2821_);
lean_dec_ref(v_toEnvExtension_2820_);
v_importedEntries_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc_ref(v_importedEntries_2831_);
lean_dec(v___x_2830_);
v_sz_2832_ = lean_array_size(v_importedEntries_2831_);
v___x_2833_ = ((size_t)0ULL);
v___x_2834_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(v_importedEntries_2831_, v_sz_2832_, v___x_2833_, v_a_2829_, v___y_2798_, v___y_2799_);
lean_dec_ref(v_importedEntries_2831_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_a_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v_arr_2838_; lean_object* v___x_2839_; uint8_t v___x_2840_; 
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_a_2835_);
lean_dec_ref(v___x_2834_);
v___x_2836_ = lean_unsigned_to_nat(0u);
v___x_2837_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__1));
v_arr_2838_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__26(v___x_2837_, v_a_2835_);
lean_dec(v_a_2835_);
v___x_2839_ = lean_array_get_size(v_arr_2838_);
v___x_2840_ = lean_nat_dec_eq(v___x_2839_, v___x_2836_);
if (v___x_2840_ == 0)
{
lean_object* v___x_2841_; lean_object* v___x_2842_; uint8_t v___x_2843_; 
v___x_2841_ = lean_unsigned_to_nat(1u);
v___x_2842_ = lean_nat_sub(v___x_2839_, v___x_2841_);
v___x_2843_ = lean_nat_dec_le(v___x_2836_, v___x_2842_);
if (v___x_2843_ == 0)
{
lean_inc(v___x_2842_);
v___y_2812_ = v_arr_2838_;
v___y_2813_ = v___x_2842_;
v___y_2814_ = v___x_2839_;
v___y_2815_ = v___x_2842_;
goto v___jp_2811_;
}
else
{
v___y_2812_ = v_arr_2838_;
v___y_2813_ = v___x_2842_;
v___y_2814_ = v___x_2839_;
v___y_2815_ = v___x_2836_;
goto v___jp_2811_;
}
}
else
{
v___y_2802_ = v_arr_2838_;
goto v___jp_2801_;
}
}
else
{
lean_object* v_a_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2851_; 
v_a_2844_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2846_ = v___x_2834_;
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_a_2844_);
lean_dec(v___x_2834_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2849_; 
if (v_isShared_2847_ == 0)
{
v___x_2849_ = v___x_2846_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_a_2844_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___boxed(lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v___y_2853_, v___y_2854_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(lean_object* v_t_2857_, lean_object* v_k_2858_, lean_object* v_fallback_2859_){
_start:
{
if (lean_obj_tag(v_t_2857_) == 0)
{
lean_object* v_k_2860_; lean_object* v_v_2861_; lean_object* v_l_2862_; lean_object* v_r_2863_; uint8_t v___x_2864_; 
v_k_2860_ = lean_ctor_get(v_t_2857_, 1);
v_v_2861_ = lean_ctor_get(v_t_2857_, 2);
v_l_2862_ = lean_ctor_get(v_t_2857_, 3);
v_r_2863_ = lean_ctor_get(v_t_2857_, 4);
v___x_2864_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2858_, v_k_2860_);
switch(v___x_2864_)
{
case 0:
{
v_t_2857_ = v_l_2862_;
goto _start;
}
case 1:
{
lean_inc(v_v_2861_);
return v_v_2861_;
}
default: 
{
v_t_2857_ = v_r_2863_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2859_);
return v_fallback_2859_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg___boxed(lean_object* v_t_2867_, lean_object* v_k_2868_, lean_object* v_fallback_2869_){
_start:
{
lean_object* v_res_2870_; 
v_res_2870_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_2867_, v_k_2868_, v_fallback_2869_);
lean_dec(v_fallback_2869_);
lean_dec(v_k_2868_);
lean_dec(v_t_2867_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(lean_object* v_as_2871_, size_t v_sz_2872_, size_t v_i_2873_, lean_object* v_b_2874_){
_start:
{
uint8_t v___x_2876_; 
v___x_2876_ = lean_usize_dec_lt(v_i_2873_, v_sz_2872_);
if (v___x_2876_ == 0)
{
lean_object* v___x_2877_; 
v___x_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2877_, 0, v_b_2874_);
return v___x_2877_;
}
else
{
lean_object* v_a_2878_; lean_object* v_fst_2879_; lean_object* v_snd_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; size_t v___x_2885_; size_t v___x_2886_; 
v_a_2878_ = lean_array_uget_borrowed(v_as_2871_, v_i_2873_);
v_fst_2879_ = lean_ctor_get(v_a_2878_, 0);
v_snd_2880_ = lean_ctor_get(v_a_2878_, 1);
v___x_2881_ = l_Lean_NameSet_empty;
v___x_2882_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_2874_, v_snd_2880_, v___x_2881_);
lean_inc(v_fst_2879_);
v___x_2883_ = l_Lean_NameSet_insert(v___x_2882_, v_fst_2879_);
lean_inc(v_snd_2880_);
v___x_2884_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_snd_2880_, v___x_2883_, v_b_2874_);
v___x_2885_ = ((size_t)1ULL);
v___x_2886_ = lean_usize_add(v_i_2873_, v___x_2885_);
v_i_2873_ = v___x_2886_;
v_b_2874_ = v___x_2884_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg___boxed(lean_object* v_as_2888_, lean_object* v_sz_2889_, lean_object* v_i_2890_, lean_object* v_b_2891_, lean_object* v___y_2892_){
_start:
{
size_t v_sz_boxed_2893_; size_t v_i_boxed_2894_; lean_object* v_res_2895_; 
v_sz_boxed_2893_ = lean_unbox_usize(v_sz_2889_);
lean_dec(v_sz_2889_);
v_i_boxed_2894_ = lean_unbox_usize(v_i_2890_);
lean_dec(v_i_2890_);
v_res_2895_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_2888_, v_sz_boxed_2893_, v_i_boxed_2894_, v_b_2891_);
lean_dec_ref(v_as_2888_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(lean_object* v_as_2896_, size_t v_sz_2897_, size_t v_i_2898_, lean_object* v_b_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_){
_start:
{
uint8_t v___x_2903_; 
v___x_2903_ = lean_usize_dec_lt(v_i_2898_, v_sz_2897_);
if (v___x_2903_ == 0)
{
lean_object* v___x_2904_; 
v___x_2904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2904_, 0, v_b_2899_);
return v___x_2904_;
}
else
{
lean_object* v_a_2905_; size_t v_sz_2906_; size_t v___x_2907_; lean_object* v___x_2908_; 
v_a_2905_ = lean_array_uget_borrowed(v_as_2896_, v_i_2898_);
v_sz_2906_ = lean_array_size(v_a_2905_);
v___x_2907_ = ((size_t)0ULL);
v___x_2908_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_a_2905_, v_sz_2906_, v___x_2907_, v_b_2899_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v_a_2909_; size_t v___x_2910_; size_t v___x_2911_; 
v_a_2909_ = lean_ctor_get(v___x_2908_, 0);
lean_inc(v_a_2909_);
lean_dec_ref(v___x_2908_);
v___x_2910_ = ((size_t)1ULL);
v___x_2911_ = lean_usize_add(v_i_2898_, v___x_2910_);
v_i_2898_ = v___x_2911_;
v_b_2899_ = v_a_2909_;
goto _start;
}
else
{
return v___x_2908_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2___boxed(lean_object* v_as_2913_, lean_object* v_sz_2914_, lean_object* v_i_2915_, lean_object* v_b_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
size_t v_sz_boxed_2920_; size_t v_i_boxed_2921_; lean_object* v_res_2922_; 
v_sz_boxed_2920_ = lean_unbox_usize(v_sz_2914_);
lean_dec(v_sz_2914_);
v_i_boxed_2921_ = lean_unbox_usize(v_i_2915_);
lean_dec(v_i_2915_);
v_res_2922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v_as_2913_, v_sz_boxed_2920_, v_i_boxed_2921_, v_b_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec_ref(v_as_2913_);
return v_res_2922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(lean_object* v_as_2923_, size_t v_i_2924_, size_t v_stop_2925_, lean_object* v_b_2926_){
_start:
{
uint8_t v___x_2927_; 
v___x_2927_ = lean_usize_dec_eq(v_i_2924_, v_stop_2925_);
if (v___x_2927_ == 0)
{
lean_object* v___x_2928_; lean_object* v_fst_2929_; lean_object* v_snd_2930_; lean_object* v___x_2931_; size_t v___x_2932_; size_t v___x_2933_; 
v___x_2928_ = lean_array_uget_borrowed(v_as_2923_, v_i_2924_);
v_fst_2929_ = lean_ctor_get(v___x_2928_, 0);
v_snd_2930_ = lean_ctor_get(v___x_2928_, 1);
lean_inc(v_snd_2930_);
lean_inc(v_fst_2929_);
v___x_2931_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2929_, v_snd_2930_, v_b_2926_);
v___x_2932_ = ((size_t)1ULL);
v___x_2933_ = lean_usize_add(v_i_2924_, v___x_2932_);
v_i_2924_ = v___x_2933_;
v_b_2926_ = v___x_2931_;
goto _start;
}
else
{
return v_b_2926_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3___boxed(lean_object* v_as_2935_, lean_object* v_i_2936_, lean_object* v_stop_2937_, lean_object* v_b_2938_){
_start:
{
size_t v_i_boxed_2939_; size_t v_stop_boxed_2940_; lean_object* v_res_2941_; 
v_i_boxed_2939_ = lean_unbox_usize(v_i_2936_);
lean_dec(v_i_2936_);
v_stop_boxed_2940_ = lean_unbox_usize(v_stop_2937_);
lean_dec(v_stop_2937_);
v_res_2941_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v_as_2935_, v_i_boxed_2939_, v_stop_boxed_2940_, v_b_2938_);
lean_dec_ref(v_as_2935_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(lean_object* v_as_2942_, size_t v_i_2943_, size_t v_stop_2944_, lean_object* v_b_2945_){
_start:
{
lean_object* v___y_2947_; uint8_t v___x_2951_; 
v___x_2951_ = lean_usize_dec_eq(v_i_2943_, v_stop_2944_);
if (v___x_2951_ == 0)
{
lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; uint8_t v___x_2955_; 
v___x_2952_ = lean_array_uget_borrowed(v_as_2942_, v_i_2943_);
v___x_2953_ = lean_unsigned_to_nat(0u);
v___x_2954_ = lean_array_get_size(v___x_2952_);
v___x_2955_ = lean_nat_dec_lt(v___x_2953_, v___x_2954_);
if (v___x_2955_ == 0)
{
v___y_2947_ = v_b_2945_;
goto v___jp_2946_;
}
else
{
uint8_t v___x_2956_; 
v___x_2956_ = lean_nat_dec_le(v___x_2954_, v___x_2954_);
if (v___x_2956_ == 0)
{
if (v___x_2955_ == 0)
{
v___y_2947_ = v_b_2945_;
goto v___jp_2946_;
}
else
{
size_t v___x_2957_; size_t v___x_2958_; lean_object* v___x_2959_; 
v___x_2957_ = ((size_t)0ULL);
v___x_2958_ = lean_usize_of_nat(v___x_2954_);
v___x_2959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_2952_, v___x_2957_, v___x_2958_, v_b_2945_);
v___y_2947_ = v___x_2959_;
goto v___jp_2946_;
}
}
else
{
size_t v___x_2960_; size_t v___x_2961_; lean_object* v___x_2962_; 
v___x_2960_ = ((size_t)0ULL);
v___x_2961_ = lean_usize_of_nat(v___x_2954_);
v___x_2962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_2952_, v___x_2960_, v___x_2961_, v_b_2945_);
v___y_2947_ = v___x_2962_;
goto v___jp_2946_;
}
}
}
else
{
return v_b_2945_;
}
v___jp_2946_:
{
size_t v___x_2948_; size_t v___x_2949_; 
v___x_2948_ = ((size_t)1ULL);
v___x_2949_ = lean_usize_add(v_i_2943_, v___x_2948_);
v_i_2943_ = v___x_2949_;
v_b_2945_ = v___y_2947_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5___boxed(lean_object* v_as_2963_, lean_object* v_i_2964_, lean_object* v_stop_2965_, lean_object* v_b_2966_){
_start:
{
size_t v_i_boxed_2967_; size_t v_stop_boxed_2968_; lean_object* v_res_2969_; 
v_i_boxed_2967_ = lean_unbox_usize(v_i_2964_);
lean_dec(v_i_2964_);
v_stop_boxed_2968_ = lean_unbox_usize(v_stop_2965_);
lean_dec(v_stop_2965_);
v_res_2969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v_as_2963_, v_i_boxed_2967_, v_stop_boxed_2968_, v_b_2966_);
lean_dec_ref(v_as_2963_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(lean_object* v___y_2970_){
_start:
{
lean_object* v___x_2972_; lean_object* v_env_2973_; lean_object* v___x_2974_; lean_object* v_ext_2975_; lean_object* v_toEnvExtension_2976_; lean_object* v_asyncMode_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v_categories_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2972_ = lean_st_ref_get(v___y_2970_);
v_env_2973_ = lean_ctor_get(v___x_2972_, 0);
lean_inc_ref(v_env_2973_);
lean_dec(v___x_2972_);
v___x_2974_ = l_Lean_Parser_parserExtension;
v_ext_2975_ = lean_ctor_get(v___x_2974_, 1);
lean_inc_ref(v_ext_2975_);
v_toEnvExtension_2976_ = lean_ctor_get(v_ext_2975_, 0);
lean_inc_ref(v_toEnvExtension_2976_);
lean_dec_ref(v_ext_2975_);
v_asyncMode_2977_ = lean_ctor_get(v_toEnvExtension_2976_, 2);
lean_inc(v_asyncMode_2977_);
lean_dec_ref(v_toEnvExtension_2976_);
v___x_2978_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_inc_ref(v_env_2973_);
v___x_2979_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2978_, v___x_2974_, v_env_2973_, v_asyncMode_2977_);
lean_dec(v_asyncMode_2977_);
v_categories_2980_ = lean_ctor_get(v___x_2979_, 2);
lean_inc_ref(v_categories_2980_);
lean_dec(v___x_2979_);
v___x_2981_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_2982_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_2980_, v___x_2981_);
if (lean_obj_tag(v___x_2982_) == 1)
{
lean_object* v_val_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_3021_; 
v_val_2983_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_2985_ = v___x_2982_;
v_isShared_2986_ = v_isSharedCheck_3021_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_val_2983_);
lean_dec(v___x_2982_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_3021_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___y_2988_; lean_object* v___x_2997_; lean_object* v_toEnvExtension_2998_; lean_object* v_exportEntriesFn_2999_; lean_object* v_asyncMode_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v_importedEntries_3005_; lean_object* v___x_3006_; uint8_t v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; uint8_t v___x_3013_; 
v___x_2997_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc_ref(v_toEnvExtension_2998_);
v_exportEntriesFn_2999_ = lean_ctor_get(v___x_2997_, 4);
lean_inc_ref(v_exportEntriesFn_2999_);
v_asyncMode_3000_ = lean_ctor_get(v_toEnvExtension_2998_, 2);
lean_inc(v_asyncMode_3000_);
v___x_3001_ = lean_box(1);
v___x_3002_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_3003_ = lean_box(0);
lean_inc_ref(v_env_2973_);
v___x_3004_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3002_, v_toEnvExtension_2998_, v_env_2973_, v_asyncMode_3000_, v___x_3003_);
lean_dec_ref(v_toEnvExtension_2998_);
v_importedEntries_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc_ref(v_importedEntries_3005_);
lean_dec(v___x_3004_);
lean_inc_ref(v_env_2973_);
v___x_3006_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3001_, v___x_2997_, v_env_2973_, v_asyncMode_3000_, v___x_3003_);
lean_dec(v_asyncMode_3000_);
v___x_3007_ = 0;
v___x_3008_ = lean_box(v___x_3007_);
v___x_3009_ = lean_apply_3(v_exportEntriesFn_2999_, v_env_2973_, v___x_3006_, v___x_3008_);
v___x_3010_ = lean_array_push(v_importedEntries_3005_, v___x_3009_);
v___x_3011_ = lean_unsigned_to_nat(0u);
v___x_3012_ = lean_array_get_size(v___x_3010_);
v___x_3013_ = lean_nat_dec_lt(v___x_3011_, v___x_3012_);
if (v___x_3013_ == 0)
{
lean_dec_ref(v___x_3010_);
v___y_2988_ = v___x_3001_;
goto v___jp_2987_;
}
else
{
uint8_t v___x_3014_; 
v___x_3014_ = lean_nat_dec_le(v___x_3012_, v___x_3012_);
if (v___x_3014_ == 0)
{
if (v___x_3013_ == 0)
{
lean_dec_ref(v___x_3010_);
v___y_2988_ = v___x_3001_;
goto v___jp_2987_;
}
else
{
size_t v___x_3015_; size_t v___x_3016_; lean_object* v___x_3017_; 
v___x_3015_ = ((size_t)0ULL);
v___x_3016_ = lean_usize_of_nat(v___x_3012_);
v___x_3017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3010_, v___x_3015_, v___x_3016_, v___x_3001_);
lean_dec_ref(v___x_3010_);
v___y_2988_ = v___x_3017_;
goto v___jp_2987_;
}
}
else
{
size_t v___x_3018_; size_t v___x_3019_; lean_object* v___x_3020_; 
v___x_3018_ = ((size_t)0ULL);
v___x_3019_ = lean_usize_of_nat(v___x_3012_);
v___x_3020_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3010_, v___x_3018_, v___x_3019_, v___x_3001_);
lean_dec_ref(v___x_3010_);
v___y_2988_ = v___x_3020_;
goto v___jp_2987_;
}
}
v___jp_2987_:
{
lean_object* v_tables_2989_; lean_object* v_leadingTable_2990_; lean_object* v_trailingTable_2991_; lean_object* v_firstTokens_2992_; lean_object* v_firstTokens_2993_; lean_object* v___x_2995_; 
v_tables_2989_ = lean_ctor_get(v_val_2983_, 2);
v_leadingTable_2990_ = lean_ctor_get(v_tables_2989_, 0);
v_trailingTable_2991_ = lean_ctor_get(v_tables_2989_, 2);
lean_inc(v_trailingTable_2991_);
lean_inc(v_leadingTable_2990_);
lean_inc(v_val_2983_);
v_firstTokens_2992_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2983_, v_leadingTable_2990_, v___y_2988_);
v_firstTokens_2993_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_2983_, v_trailingTable_2991_, v_firstTokens_2992_);
if (v_isShared_2986_ == 0)
{
lean_ctor_set_tag(v___x_2985_, 0);
lean_ctor_set(v___x_2985_, 0, v_firstTokens_2993_);
v___x_2995_ = v___x_2985_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_firstTokens_2993_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
return v___x_2995_;
}
}
}
}
else
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
lean_dec(v___x_2982_);
lean_dec_ref(v_env_2973_);
v___x_3022_ = lean_box(1);
v___x_3023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3022_);
return v___x_3023_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg___boxed(lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_3024_);
lean_dec(v___y_3024_);
return v_res_3026_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0(void){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3027_ = lean_box(1);
v___x_3028_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_3027_);
return v___x_3028_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2(void){
_start:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3030_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1));
v___x_3031_ = l_Lean_stringToMessageData(v___x_3030_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(lean_object* v_a_3032_, lean_object* v_a_3033_){
_start:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v_env_3038_; lean_object* v_env_3039_; lean_object* v_env_3040_; lean_object* v___x_3041_; lean_object* v_toEnvExtension_3042_; lean_object* v_exportEntriesFn_3043_; lean_object* v_asyncMode_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v_importedEntries_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3102_; 
v___x_3035_ = lean_st_ref_get(v_a_3033_);
v___x_3036_ = lean_st_ref_get(v_a_3033_);
v___x_3037_ = lean_st_ref_get(v_a_3033_);
v_env_3038_ = lean_ctor_get(v___x_3035_, 0);
lean_inc_ref(v_env_3038_);
lean_dec(v___x_3035_);
v_env_3039_ = lean_ctor_get(v___x_3036_, 0);
lean_inc_ref(v_env_3039_);
lean_dec(v___x_3036_);
v_env_3040_ = lean_ctor_get(v___x_3037_, 0);
lean_inc_ref(v_env_3040_);
lean_dec(v___x_3037_);
v___x_3041_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_3042_ = lean_ctor_get(v___x_3041_, 0);
lean_inc_ref(v_toEnvExtension_3042_);
v_exportEntriesFn_3043_ = lean_ctor_get(v___x_3041_, 4);
lean_inc_ref(v_exportEntriesFn_3043_);
v_asyncMode_3044_ = lean_ctor_get(v_toEnvExtension_3042_, 2);
lean_inc(v_asyncMode_3044_);
v___x_3045_ = lean_box(1);
v___x_3046_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0);
v___x_3047_ = lean_box(0);
v___x_3048_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3046_, v_toEnvExtension_3042_, v_env_3038_, v_asyncMode_3044_, v___x_3047_);
lean_dec_ref(v_toEnvExtension_3042_);
v_importedEntries_3049_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3102_ == 0)
{
lean_object* v_unused_3103_; 
v_unused_3103_ = lean_ctor_get(v___x_3048_, 1);
lean_dec(v_unused_3103_);
v___x_3051_ = v___x_3048_;
v_isShared_3052_ = v_isSharedCheck_3102_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_importedEntries_3049_);
lean_dec(v___x_3048_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3102_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3053_; uint8_t v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; size_t v_sz_3058_; size_t v___x_3059_; lean_object* v___x_3060_; 
v___x_3053_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3045_, v___x_3041_, v_env_3040_, v_asyncMode_3044_, v___x_3047_);
lean_dec(v_asyncMode_3044_);
v___x_3054_ = 0;
v___x_3055_ = lean_box(v___x_3054_);
v___x_3056_ = lean_apply_3(v_exportEntriesFn_3043_, v_env_3039_, v___x_3053_, v___x_3055_);
v___x_3057_ = lean_array_push(v_importedEntries_3049_, v___x_3056_);
v_sz_3058_ = lean_array_size(v___x_3057_);
v___x_3059_ = ((size_t)0ULL);
v___x_3060_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v___x_3057_, v_sz_3058_, v___x_3059_, v___x_3045_, v_a_3032_, v_a_3033_);
lean_dec_ref(v___x_3057_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_object* v_a_3061_; lean_object* v___x_3062_; lean_object* v_a_3063_; lean_object* v___x_3064_; 
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
lean_inc(v_a_3061_);
lean_dec_ref(v___x_3060_);
v___x_3062_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v_a_3033_);
v_a_3063_ = lean_ctor_get(v___x_3062_, 0);
lean_inc(v_a_3063_);
lean_dec_ref(v___x_3062_);
v___x_3064_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v_a_3032_, v_a_3033_);
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_object* v_a_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v_a_3065_ = lean_ctor_get(v___x_3064_, 0);
lean_inc(v_a_3065_);
lean_dec_ref(v___x_3064_);
v___x_3066_ = lean_box(0);
v___x_3067_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_3063_, v_a_3061_, v_a_3065_, v___x_3066_, v_a_3032_, v_a_3033_);
lean_dec(v_a_3061_);
lean_dec(v_a_3063_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v_a_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3073_; 
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_a_3068_);
lean_dec_ref(v___x_3067_);
v___x_3069_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2);
v___x_3070_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_3071_ = l_Lean_MessageData_joinSep(v_a_3068_, v___x_3070_);
if (v_isShared_3052_ == 0)
{
lean_ctor_set_tag(v___x_3051_, 7);
lean_ctor_set(v___x_3051_, 1, v___x_3071_);
lean_ctor_set(v___x_3051_, 0, v___x_3070_);
v___x_3073_ = v___x_3051_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v___x_3070_);
lean_ctor_set(v_reuseFailAlloc_3077_, 1, v___x_3071_);
v___x_3073_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3074_ = l_Lean_MessageData_nestD(v___x_3073_);
v___x_3075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3069_);
lean_ctor_set(v___x_3075_, 1, v___x_3074_);
v___x_3076_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v___x_3075_, v_a_3032_, v_a_3033_);
return v___x_3076_;
}
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
lean_del_object(v___x_3051_);
lean_dec_ref(v_a_3032_);
v_a_3078_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_3067_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3067_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
else
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3093_; 
lean_dec(v_a_3063_);
lean_dec(v_a_3061_);
lean_del_object(v___x_3051_);
lean_dec_ref(v_a_3032_);
v_a_3086_ = lean_ctor_get(v___x_3064_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v___x_3064_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_3064_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3091_; 
if (v_isShared_3089_ == 0)
{
v___x_3091_ = v___x_3088_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3086_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
}
else
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3101_; 
lean_del_object(v___x_3051_);
lean_dec_ref(v_a_3032_);
v_a_3094_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3096_ = v___x_3060_;
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3060_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3099_; 
if (v_isShared_3097_ == 0)
{
v___x_3099_ = v___x_3096_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___boxed(lean_object* v_a_3104_, lean_object* v_a_3105_, lean_object* v_a_3106_){
_start:
{
lean_object* v_res_3107_; 
v_res_3107_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_3104_, v_a_3105_);
lean_dec(v_a_3105_);
return v_res_3107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags(lean_object* v___stx_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_){
_start:
{
lean_object* v___x_3112_; 
v___x_3112_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_3109_, v_a_3110_);
return v___x_3112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed(lean_object* v___stx_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_, lean_object* v_a_3116_){
_start:
{
lean_object* v_res_3117_; 
v_res_3117_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags(v___stx_3113_, v_a_3114_, v_a_3115_);
lean_dec(v_a_3115_);
lean_dec(v___stx_3113_);
return v_res_3117_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(lean_object* v_00_u03b4_3118_, lean_object* v_t_3119_, lean_object* v_k_3120_, lean_object* v_fallback_3121_){
_start:
{
lean_object* v___x_3122_; 
v___x_3122_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_3119_, v_k_3120_, v_fallback_3121_);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___boxed(lean_object* v_00_u03b4_3123_, lean_object* v_t_3124_, lean_object* v_k_3125_, lean_object* v_fallback_3126_){
_start:
{
lean_object* v_res_3127_; 
v_res_3127_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(v_00_u03b4_3123_, v_t_3124_, v_k_3125_, v_fallback_3126_);
lean_dec(v_fallback_3126_);
lean_dec(v_k_3125_);
lean_dec(v_t_3124_);
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(lean_object* v_as_3128_, size_t v_sz_3129_, size_t v_i_3130_, lean_object* v_b_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_){
_start:
{
lean_object* v___x_3135_; 
v___x_3135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_3128_, v_sz_3129_, v_i_3130_, v_b_3131_);
return v___x_3135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___boxed(lean_object* v_as_3136_, lean_object* v_sz_3137_, lean_object* v_i_3138_, lean_object* v_b_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_){
_start:
{
size_t v_sz_boxed_3143_; size_t v_i_boxed_3144_; lean_object* v_res_3145_; 
v_sz_boxed_3143_ = lean_unbox_usize(v_sz_3137_);
lean_dec(v_sz_3137_);
v_i_boxed_3144_ = lean_unbox_usize(v_i_3138_);
lean_dec(v_i_3138_);
v_res_3145_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(v_as_3136_, v_sz_boxed_3143_, v_i_boxed_3144_, v_b_3139_, v___y_3140_, v___y_3141_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec_ref(v_as_3136_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(lean_object* v___y_3146_, lean_object* v___y_3147_){
_start:
{
lean_object* v___x_3149_; 
v___x_3149_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_3147_);
return v___x_3149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___boxed(lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_){
_start:
{
lean_object* v_res_3153_; 
v_res_3153_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(v___y_3150_, v___y_3151_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
return v_res_3153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(lean_object* v_val_3154_, lean_object* v___x_3155_, lean_object* v___x_3156_, lean_object* v_inst_3157_, lean_object* v_R_3158_, lean_object* v_a_3159_, lean_object* v_b_3160_){
_start:
{
lean_object* v___x_3161_; 
v___x_3161_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_3154_, v___x_3155_, v___x_3156_, v_a_3159_, v_b_3160_);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___boxed(lean_object* v_val_3162_, lean_object* v___x_3163_, lean_object* v___x_3164_, lean_object* v_inst_3165_, lean_object* v_R_3166_, lean_object* v_a_3167_, lean_object* v_b_3168_){
_start:
{
lean_object* v_res_3169_; 
v_res_3169_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(v_val_3162_, v___x_3163_, v___x_3164_, v_inst_3165_, v_R_3166_, v_a_3167_, v_b_3168_);
lean_dec_ref(v___x_3163_);
lean_dec_ref(v_val_3162_);
return v_res_3169_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8(lean_object* v_init_3170_, lean_object* v_t_3171_){
_start:
{
lean_object* v___x_3172_; 
v___x_3172_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__17(v_init_3170_, v_t_3171_);
return v___x_3172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(lean_object* v_n_3173_, lean_object* v_as_3174_, lean_object* v_lo_3175_, lean_object* v_hi_3176_, lean_object* v_w_3177_, lean_object* v_hlo_3178_, lean_object* v_hhi_3179_){
_start:
{
lean_object* v___x_3180_; 
v___x_3180_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_as_3174_, v_lo_3175_, v_hi_3176_);
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___boxed(lean_object* v_n_3181_, lean_object* v_as_3182_, lean_object* v_lo_3183_, lean_object* v_hi_3184_, lean_object* v_w_3185_, lean_object* v_hlo_3186_, lean_object* v_hhi_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(v_n_3181_, v_as_3182_, v_lo_3183_, v_hi_3184_, v_w_3185_, v_hlo_3186_, v_hhi_3187_);
lean_dec(v_hi_3184_);
lean_dec(v_n_3181_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(lean_object* v_00_u03b2_3189_, lean_object* v_x_3190_, lean_object* v_x_3191_){
_start:
{
lean_object* v___x_3192_; 
v___x_3192_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_3190_, v_x_3191_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3193_, lean_object* v_x_3194_, lean_object* v_x_3195_){
_start:
{
lean_object* v_res_3196_; 
v_res_3196_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(v_00_u03b2_3193_, v_x_3194_, v_x_3195_);
lean_dec(v_x_3195_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(lean_object* v_tac_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_){
_start:
{
lean_object* v___x_3201_; 
v___x_3201_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_3197_, v___y_3199_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___boxed(lean_object* v_tac_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_){
_start:
{
lean_object* v_res_3206_; 
v_res_3206_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(v_tac_3202_, v___y_3203_, v___y_3204_);
lean_dec(v___y_3204_);
lean_dec_ref(v___y_3203_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(lean_object* v_00_u03b2_3207_, lean_object* v_k_3208_, lean_object* v_v_3209_, lean_object* v_t_3210_, lean_object* v_hl_3211_){
_start:
{
lean_object* v___x_3212_; 
v___x_3212_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_k_3208_, v_v_3209_, v_t_3210_);
return v___x_3212_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(lean_object* v_as_3213_, lean_object* v_as_x27_3214_, lean_object* v_b_3215_, lean_object* v_a_3216_){
_start:
{
lean_object* v___x_3217_; 
v___x_3217_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_as_x27_3214_, v_b_3215_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___boxed(lean_object* v_as_3218_, lean_object* v_as_x27_3219_, lean_object* v_b_3220_, lean_object* v_a_3221_){
_start:
{
lean_object* v_res_3222_; 
v_res_3222_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(v_as_3218_, v_as_x27_3219_, v_b_3220_, v_a_3221_);
lean_dec(v_as_3218_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(lean_object* v_00_u03b4_3223_, lean_object* v_t_3224_, lean_object* v_k_3225_){
_start:
{
lean_object* v___x_3226_; 
v___x_3226_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg(v_t_3224_, v_k_3225_);
return v___x_3226_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___boxed(lean_object* v_00_u03b4_3227_, lean_object* v_t_3228_, lean_object* v_k_3229_){
_start:
{
lean_object* v_res_3230_; 
v_res_3230_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(v_00_u03b4_3227_, v_t_3228_, v_k_3229_);
lean_dec(v_k_3229_);
lean_dec(v_t_3228_);
return v_res_3230_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13(lean_object* v_00_u03b2_3231_, lean_object* v_x_3232_, lean_object* v_x_3233_){
_start:
{
lean_object* v___x_3234_; 
v___x_3234_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___redArg(v_x_3232_, v_x_3233_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___boxed(lean_object* v_00_u03b2_3235_, lean_object* v_x_3236_, lean_object* v_x_3237_){
_start:
{
lean_object* v_res_3238_; 
v_res_3238_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13(v_00_u03b2_3235_, v_x_3236_, v_x_3237_);
lean_dec(v_x_3237_);
return v_res_3238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(lean_object* v_as_3239_, size_t v_sz_3240_, size_t v_i_3241_, lean_object* v_b_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_){
_start:
{
lean_object* v___x_3246_; 
v___x_3246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___redArg(v_as_3239_, v_sz_3240_, v_i_3241_, v_b_3242_);
return v___x_3246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20___boxed(lean_object* v_as_3247_, lean_object* v_sz_3248_, lean_object* v_i_3249_, lean_object* v_b_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_){
_start:
{
size_t v_sz_boxed_3254_; size_t v_i_boxed_3255_; lean_object* v_res_3256_; 
v_sz_boxed_3254_ = lean_unbox_usize(v_sz_3248_);
lean_dec(v_sz_3248_);
v_i_boxed_3255_ = lean_unbox_usize(v_i_3249_);
lean_dec(v_i_3249_);
v_res_3256_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__20(v_as_3247_, v_sz_boxed_3254_, v_i_boxed_3255_, v_b_3250_, v___y_3251_, v___y_3252_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
lean_dec_ref(v_as_3247_);
return v_res_3256_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(lean_object* v_init_3257_, lean_object* v_t_3258_){
_start:
{
lean_object* v___x_3259_; 
v___x_3259_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22_spec__26(v_init_3257_, v_t_3258_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___boxed(lean_object* v_init_3260_, lean_object* v_t_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(v_init_3260_, v_t_3261_);
lean_dec(v_t_3261_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(lean_object* v_n_3263_, lean_object* v_as_3264_, lean_object* v_lo_3265_, lean_object* v_hi_3266_, lean_object* v_w_3267_, lean_object* v_hlo_3268_, lean_object* v_hhi_3269_){
_start:
{
lean_object* v___x_3270_; 
v___x_3270_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___redArg(v_as_3264_, v_lo_3265_, v_hi_3266_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___boxed(lean_object* v_n_3271_, lean_object* v_as_3272_, lean_object* v_lo_3273_, lean_object* v_hi_3274_, lean_object* v_w_3275_, lean_object* v_hlo_3276_, lean_object* v_hhi_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(v_n_3271_, v_as_3272_, v_lo_3273_, v_hi_3274_, v_w_3275_, v_hlo_3276_, v_hhi_3277_);
lean_dec(v_hi_3274_);
lean_dec(v_n_3271_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24(lean_object* v_init_3279_, lean_object* v_x_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
lean_object* v___x_3284_; 
v___x_3284_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg(v_init_3279_, v_x_3280_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___boxed(lean_object* v_init_3285_, lean_object* v_x_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24(v_init_3285_, v_x_3286_, v___y_3287_, v___y_3288_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_3291_, lean_object* v_x_3292_, size_t v_x_3293_, lean_object* v_x_3294_){
_start:
{
lean_object* v___x_3295_; 
v___x_3295_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_3292_, v_x_3293_, v_x_3294_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_3296_, lean_object* v_x_3297_, lean_object* v_x_3298_, lean_object* v_x_3299_){
_start:
{
size_t v_x_21130__boxed_3300_; lean_object* v_res_3301_; 
v_x_21130__boxed_3300_ = lean_unbox_usize(v_x_3298_);
lean_dec(v_x_3298_);
v_res_3301_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(v_00_u03b2_3296_, v_x_3297_, v_x_21130__boxed_3300_, v_x_3299_);
lean_dec(v_x_3299_);
return v_res_3301_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(lean_object* v_as_3302_, lean_object* v_k_3303_, lean_object* v_x_3304_, lean_object* v_x_3305_, lean_object* v_x_3306_){
_start:
{
lean_object* v___x_3307_; 
v___x_3307_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_3302_, v_k_3303_, v_x_3304_, v_x_3305_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___boxed(lean_object* v_as_3308_, lean_object* v_k_3309_, lean_object* v_x_3310_, lean_object* v_x_3311_, lean_object* v_x_3312_){
_start:
{
lean_object* v_res_3313_; 
v_res_3313_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(v_as_3308_, v_k_3309_, v_x_3310_, v_x_3311_, v_x_3312_);
lean_dec_ref(v_k_3309_);
lean_dec_ref(v_as_3308_);
return v_res_3313_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16(lean_object* v_00_u03b2_3314_, lean_object* v_m_3315_, lean_object* v_a_3316_){
_start:
{
lean_object* v___x_3317_; 
v___x_3317_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg(v_m_3315_, v_a_3316_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___boxed(lean_object* v_00_u03b2_3318_, lean_object* v_m_3319_, lean_object* v_a_3320_){
_start:
{
lean_object* v_res_3321_; 
v_res_3321_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16(v_00_u03b2_3318_, v_m_3319_, v_a_3320_);
lean_dec(v_a_3320_);
lean_dec_ref(v_m_3319_);
return v_res_3321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(lean_object* v_00_u03b2_3322_, lean_object* v_keys_3323_, lean_object* v_vals_3324_, lean_object* v_heq_3325_, lean_object* v_i_3326_, lean_object* v_k_3327_){
_start:
{
lean_object* v___x_3328_; 
v___x_3328_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_3323_, v_vals_3324_, v_i_3326_, v_k_3327_);
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___boxed(lean_object* v_00_u03b2_3329_, lean_object* v_keys_3330_, lean_object* v_vals_3331_, lean_object* v_heq_3332_, lean_object* v_i_3333_, lean_object* v_k_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(v_00_u03b2_3329_, v_keys_3330_, v_vals_3331_, v_heq_3332_, v_i_3333_, v_k_3334_);
lean_dec(v_k_3334_);
lean_dec_ref(v_vals_3331_);
lean_dec_ref(v_keys_3330_);
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24(lean_object* v_00_u03b2_3336_, lean_object* v_a_3337_, lean_object* v_x_3338_){
_start:
{
lean_object* v___x_3339_; 
v___x_3339_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___redArg(v_a_3337_, v_x_3338_);
return v___x_3339_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___boxed(lean_object* v_00_u03b2_3340_, lean_object* v_a_3341_, lean_object* v_x_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24(v_00_u03b2_3340_, v_a_3341_, v_x_3342_);
lean_dec(v_x_3342_);
lean_dec(v_a_3341_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1(){
_start:
{
lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___x_3358_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3359_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1));
v___x_3360_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3361_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed), 4, 0);
v___x_3362_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3358_, v___x_3359_, v___x_3360_, v___x_3361_);
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___boxed(lean_object* v_a_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
return v_res_3364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3(){
_start:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3367_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3368_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0));
v___x_3369_ = l_Lean_addBuiltinDocString(v___x_3367_, v___x_3368_);
return v___x_3369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___boxed(lean_object* v_a_3370_){
_start:
{
lean_object* v_res_3371_; 
v_res_3371_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5(){
_start:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3398_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3399_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6));
v___x_3400_ = l_Lean_addBuiltinDeclarationRanges(v___x_3398_, v___x_3399_);
return v___x_3400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___boxed(lean_object* v_a_3401_){
_start:
{
lean_object* v_res_3402_; 
v_res_3402_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(lean_object* v_env_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, uint8_t v_includeUnnamed_3406_, lean_object* v_x_3407_, lean_object* v_____s_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v_fst_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3467_; 
v_fst_3414_ = lean_ctor_get(v_x_3407_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v_x_3407_);
if (v_isSharedCheck_3467_ == 0)
{
lean_object* v_unused_3468_; 
v_unused_3468_ = lean_ctor_get(v_x_3407_, 1);
lean_dec(v_unused_3468_);
v___x_3416_ = v_x_3407_;
v_isShared_3417_ = v_isSharedCheck_3467_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_fst_3414_);
lean_dec(v_x_3407_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3467_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v_userName_3419_; lean_object* v___y_3420_; lean_object* v___x_3452_; 
lean_inc(v_fst_3414_);
lean_inc_ref(v_env_3403_);
v___x_3452_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_3403_, v_fst_3414_);
if (lean_obj_tag(v___x_3452_) == 1)
{
lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3460_; 
lean_del_object(v___x_3416_);
lean_dec(v_fst_3414_);
lean_dec_ref(v_env_3403_);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3460_ == 0)
{
lean_object* v_unused_3461_; 
v_unused_3461_ = lean_ctor_get(v___x_3452_, 0);
lean_dec(v_unused_3461_);
v___x_3454_ = v___x_3452_;
v_isShared_3455_ = v_isSharedCheck_3460_;
goto v_resetjp_3453_;
}
else
{
lean_dec(v___x_3452_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3460_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3457_; 
if (v_isShared_3455_ == 0)
{
lean_ctor_set(v___x_3454_, 0, v_____s_3408_);
v___x_3457_ = v___x_3454_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_____s_3408_);
v___x_3457_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
lean_object* v___x_3458_; 
v___x_3458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3457_);
return v___x_3458_;
}
}
}
else
{
lean_object* v___x_3462_; 
lean_dec(v___x_3452_);
v___x_3462_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg(v_a_3405_, v_fst_3414_);
if (lean_obj_tag(v___x_3462_) == 1)
{
lean_object* v_val_3463_; 
v_val_3463_ = lean_ctor_get(v___x_3462_, 0);
lean_inc(v_val_3463_);
lean_dec_ref(v___x_3462_);
v_userName_3419_ = v_val_3463_;
v___y_3420_ = v___y_3411_;
goto v___jp_3418_;
}
else
{
lean_dec(v___x_3462_);
if (v_includeUnnamed_3406_ == 0)
{
lean_object* v___x_3464_; lean_object* v___x_3465_; 
lean_del_object(v___x_3416_);
lean_dec(v_fst_3414_);
lean_dec_ref(v_env_3403_);
v___x_3464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3464_, 0, v_____s_3408_);
v___x_3465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3464_);
return v___x_3465_;
}
else
{
lean_object* v___x_3466_; 
lean_inc(v_fst_3414_);
v___x_3466_ = l_Lean_Name_toString(v_fst_3414_, v_includeUnnamed_3406_);
v_userName_3419_ = v___x_3466_;
v___y_3420_ = v___y_3411_;
goto v___jp_3418_;
}
}
}
v___jp_3418_:
{
uint8_t v___x_3421_; lean_object* v___x_3422_; 
v___x_3421_ = 1;
lean_inc(v_fst_3414_);
lean_inc_ref(v_env_3403_);
v___x_3422_ = l_Lean_findDocString_x3f(v_env_3403_, v_fst_3414_, v___x_3421_);
if (lean_obj_tag(v___x_3422_) == 0)
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3436_; 
lean_del_object(v___x_3416_);
v_a_3423_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3425_ = v___x_3422_;
v_isShared_3426_ = v_isSharedCheck_3436_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3422_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3436_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3434_; 
v___x_3427_ = l_Lean_NameSet_empty;
v___x_3428_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_a_3404_, v_fst_3414_, v___x_3427_);
lean_inc(v_fst_3414_);
v___x_3429_ = l_Lean_Parser_Tactic_Doc_getTacticExtensions(v_env_3403_, v_fst_3414_);
v___x_3430_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3430_, 0, v_fst_3414_);
lean_ctor_set(v___x_3430_, 1, v_userName_3419_);
lean_ctor_set(v___x_3430_, 2, v___x_3428_);
lean_ctor_set(v___x_3430_, 3, v_a_3423_);
lean_ctor_set(v___x_3430_, 4, v___x_3429_);
v___x_3431_ = lean_array_push(v_____s_3408_, v___x_3430_);
v___x_3432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3431_);
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 0, v___x_3432_);
v___x_3434_ = v___x_3425_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v___x_3432_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
return v___x_3434_;
}
}
}
else
{
lean_object* v_a_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3451_; 
lean_dec_ref(v_userName_3419_);
lean_dec(v_fst_3414_);
lean_dec_ref(v_____s_3408_);
lean_dec_ref(v_env_3403_);
v_a_3437_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3439_ = v___x_3422_;
v_isShared_3440_ = v_isSharedCheck_3451_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_a_3437_);
lean_dec(v___x_3422_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3451_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v_ref_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3446_; 
v_ref_3441_ = lean_ctor_get(v___y_3420_, 5);
v___x_3442_ = lean_io_error_to_string(v_a_3437_);
v___x_3443_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3442_);
v___x_3444_ = l_Lean_MessageData_ofFormat(v___x_3443_);
lean_inc(v_ref_3441_);
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 1, v___x_3444_);
lean_ctor_set(v___x_3416_, 0, v_ref_3441_);
v___x_3446_ = v___x_3416_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_ref_3441_);
lean_ctor_set(v_reuseFailAlloc_3450_, 1, v___x_3444_);
v___x_3446_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
lean_object* v___x_3448_; 
if (v_isShared_3440_ == 0)
{
lean_ctor_set(v___x_3439_, 0, v___x_3446_);
v___x_3448_ = v___x_3439_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3449_; 
v_reuseFailAlloc_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3449_, 0, v___x_3446_);
v___x_3448_ = v_reuseFailAlloc_3449_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
return v___x_3448_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed(lean_object* v_env_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_includeUnnamed_3472_, lean_object* v_x_3473_, lean_object* v_____s_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_){
_start:
{
uint8_t v_includeUnnamed_boxed_3480_; lean_object* v_res_3481_; 
v_includeUnnamed_boxed_3480_ = lean_unbox(v_includeUnnamed_3472_);
v_res_3481_ = l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(v_env_3469_, v_a_3470_, v_a_3471_, v_includeUnnamed_boxed_3480_, v_x_3473_, v_____s_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_);
lean_dec(v___y_3478_);
lean_dec_ref(v___y_3477_);
lean_dec(v___y_3476_);
lean_dec_ref(v___y_3475_);
lean_dec(v_a_3471_);
lean_dec(v_a_3470_);
return v_res_3481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(lean_object* v_as_3482_, size_t v_sz_3483_, size_t v_i_3484_, lean_object* v_b_3485_){
_start:
{
uint8_t v___x_3487_; 
v___x_3487_ = lean_usize_dec_lt(v_i_3484_, v_sz_3483_);
if (v___x_3487_ == 0)
{
lean_object* v___x_3488_; 
v___x_3488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3488_, 0, v_b_3485_);
return v___x_3488_;
}
else
{
lean_object* v_a_3489_; lean_object* v_fst_3490_; lean_object* v_snd_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; size_t v___x_3496_; size_t v___x_3497_; 
v_a_3489_ = lean_array_uget_borrowed(v_as_3482_, v_i_3484_);
v_fst_3490_ = lean_ctor_get(v_a_3489_, 0);
v_snd_3491_ = lean_ctor_get(v_a_3489_, 1);
v___x_3492_ = l_Lean_NameSet_empty;
v___x_3493_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_3485_, v_fst_3490_, v___x_3492_);
lean_inc(v_snd_3491_);
v___x_3494_ = l_Lean_NameSet_insert(v___x_3493_, v_snd_3491_);
lean_inc(v_fst_3490_);
v___x_3495_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3490_, v___x_3494_, v_b_3485_);
v___x_3496_ = ((size_t)1ULL);
v___x_3497_ = lean_usize_add(v_i_3484_, v___x_3496_);
v_i_3484_ = v___x_3497_;
v_b_3485_ = v___x_3495_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg___boxed(lean_object* v_as_3499_, lean_object* v_sz_3500_, lean_object* v_i_3501_, lean_object* v_b_3502_, lean_object* v___y_3503_){
_start:
{
size_t v_sz_boxed_3504_; size_t v_i_boxed_3505_; lean_object* v_res_3506_; 
v_sz_boxed_3504_ = lean_unbox_usize(v_sz_3500_);
lean_dec(v_sz_3500_);
v_i_boxed_3505_ = lean_unbox_usize(v_i_3501_);
lean_dec(v_i_3501_);
v_res_3506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_3499_, v_sz_boxed_3504_, v_i_boxed_3505_, v_b_3502_);
lean_dec_ref(v_as_3499_);
return v_res_3506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(lean_object* v_as_3507_, size_t v_sz_3508_, size_t v_i_3509_, lean_object* v_b_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_){
_start:
{
uint8_t v___x_3516_; 
v___x_3516_ = lean_usize_dec_lt(v_i_3509_, v_sz_3508_);
if (v___x_3516_ == 0)
{
lean_object* v___x_3517_; 
v___x_3517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3517_, 0, v_b_3510_);
return v___x_3517_;
}
else
{
lean_object* v_a_3518_; size_t v_sz_3519_; size_t v___x_3520_; lean_object* v___x_3521_; 
v_a_3518_ = lean_array_uget_borrowed(v_as_3507_, v_i_3509_);
v_sz_3519_ = lean_array_size(v_a_3518_);
v___x_3520_ = ((size_t)0ULL);
v___x_3521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_a_3518_, v_sz_3519_, v___x_3520_, v_b_3510_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_a_3522_; size_t v___x_3523_; size_t v___x_3524_; 
v_a_3522_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_a_3522_);
lean_dec_ref(v___x_3521_);
v___x_3523_ = ((size_t)1ULL);
v___x_3524_ = lean_usize_add(v_i_3509_, v___x_3523_);
v_i_3509_ = v___x_3524_;
v_b_3510_ = v_a_3522_;
goto _start;
}
else
{
return v___x_3521_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1___boxed(lean_object* v_as_3526_, lean_object* v_sz_3527_, lean_object* v_i_3528_, lean_object* v_b_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
size_t v_sz_boxed_3535_; size_t v_i_boxed_3536_; lean_object* v_res_3537_; 
v_sz_boxed_3535_ = lean_unbox_usize(v_sz_3527_);
lean_dec(v_sz_3527_);
v_i_boxed_3536_ = lean_unbox_usize(v_i_3528_);
lean_dec(v_i_3528_);
v_res_3537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v_as_3526_, v_sz_boxed_3535_, v_i_boxed_3536_, v_b_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
lean_dec_ref(v_as_3526_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(lean_object* v_f_3538_, lean_object* v_keys_3539_, lean_object* v_vals_3540_, lean_object* v_i_3541_, lean_object* v_acc_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v___x_3548_; uint8_t v___x_3549_; 
v___x_3548_ = lean_array_get_size(v_keys_3539_);
v___x_3549_ = lean_nat_dec_lt(v_i_3541_, v___x_3548_);
if (v___x_3549_ == 0)
{
lean_object* v___x_3550_; lean_object* v___x_3551_; 
lean_dec(v___y_3546_);
lean_dec_ref(v___y_3545_);
lean_dec(v___y_3544_);
lean_dec_ref(v___y_3543_);
lean_dec(v_i_3541_);
lean_dec_ref(v_f_3538_);
v___x_3550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3550_, 0, v_acc_3542_);
v___x_3551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3550_);
return v___x_3551_;
}
else
{
lean_object* v_k_3552_; lean_object* v_v_3553_; lean_object* v___x_3554_; 
v_k_3552_ = lean_array_fget_borrowed(v_keys_3539_, v_i_3541_);
v_v_3553_ = lean_array_fget_borrowed(v_vals_3540_, v_i_3541_);
lean_inc_ref(v_f_3538_);
lean_inc(v___y_3546_);
lean_inc_ref(v___y_3545_);
lean_inc(v___y_3544_);
lean_inc_ref(v___y_3543_);
lean_inc(v_v_3553_);
lean_inc(v_k_3552_);
v___x_3554_ = lean_apply_8(v_f_3538_, v_acc_3542_, v_k_3552_, v_v_3553_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_, lean_box(0));
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v_a_3555_; 
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
lean_inc(v_a_3555_);
if (lean_obj_tag(v_a_3555_) == 0)
{
lean_dec_ref(v_a_3555_);
lean_dec(v___y_3546_);
lean_dec_ref(v___y_3545_);
lean_dec(v___y_3544_);
lean_dec_ref(v___y_3543_);
lean_dec(v_i_3541_);
lean_dec_ref(v_f_3538_);
return v___x_3554_;
}
else
{
lean_object* v_a_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; 
lean_dec_ref(v___x_3554_);
v_a_3556_ = lean_ctor_get(v_a_3555_, 0);
lean_inc(v_a_3556_);
lean_dec_ref(v_a_3555_);
v___x_3557_ = lean_unsigned_to_nat(1u);
v___x_3558_ = lean_nat_add(v_i_3541_, v___x_3557_);
lean_dec(v_i_3541_);
v_i_3541_ = v___x_3558_;
v_acc_3542_ = v_a_3556_;
goto _start;
}
}
else
{
lean_dec(v___y_3546_);
lean_dec_ref(v___y_3545_);
lean_dec(v___y_3544_);
lean_dec_ref(v___y_3543_);
lean_dec(v_i_3541_);
lean_dec_ref(v_f_3538_);
return v___x_3554_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_f_3560_, lean_object* v_keys_3561_, lean_object* v_vals_3562_, lean_object* v_i_3563_, lean_object* v_acc_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_){
_start:
{
lean_object* v_res_3570_; 
v_res_3570_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3560_, v_keys_3561_, v_vals_3562_, v_i_3563_, v_acc_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_);
lean_dec_ref(v_vals_3562_);
lean_dec_ref(v_keys_3561_);
return v_res_3570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(lean_object* v_f_3571_, lean_object* v_x_3572_, lean_object* v_x_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_){
_start:
{
if (lean_obj_tag(v_x_3572_) == 0)
{
lean_object* v_es_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3601_; 
v_es_3579_ = lean_ctor_get(v_x_3572_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v_x_3572_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3581_ = v_x_3572_;
v_isShared_3582_ = v_isSharedCheck_3601_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_es_3579_);
lean_dec(v_x_3572_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3601_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; uint8_t v___x_3585_; 
v___x_3583_ = lean_unsigned_to_nat(0u);
v___x_3584_ = lean_array_get_size(v_es_3579_);
v___x_3585_ = lean_nat_dec_lt(v___x_3583_, v___x_3584_);
if (v___x_3585_ == 0)
{
lean_object* v___x_3587_; 
lean_dec_ref(v_es_3579_);
lean_dec(v___y_3577_);
lean_dec_ref(v___y_3576_);
lean_dec(v___y_3575_);
lean_dec_ref(v___y_3574_);
lean_dec_ref(v_f_3571_);
if (v_isShared_3582_ == 0)
{
lean_ctor_set_tag(v___x_3581_, 1);
lean_ctor_set(v___x_3581_, 0, v_x_3573_);
v___x_3587_ = v___x_3581_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_x_3573_);
v___x_3587_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
lean_object* v___x_3588_; 
v___x_3588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3587_);
return v___x_3588_;
}
}
else
{
uint8_t v___x_3590_; 
v___x_3590_ = lean_nat_dec_le(v___x_3584_, v___x_3584_);
if (v___x_3590_ == 0)
{
if (v___x_3585_ == 0)
{
lean_object* v___x_3592_; 
lean_dec_ref(v_es_3579_);
lean_dec(v___y_3577_);
lean_dec_ref(v___y_3576_);
lean_dec(v___y_3575_);
lean_dec_ref(v___y_3574_);
lean_dec_ref(v_f_3571_);
if (v_isShared_3582_ == 0)
{
lean_ctor_set_tag(v___x_3581_, 1);
lean_ctor_set(v___x_3581_, 0, v_x_3573_);
v___x_3592_ = v___x_3581_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_x_3573_);
v___x_3592_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
lean_object* v___x_3593_; 
v___x_3593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3592_);
return v___x_3593_;
}
}
else
{
size_t v___x_3595_; size_t v___x_3596_; lean_object* v___x_3597_; 
lean_del_object(v___x_3581_);
v___x_3595_ = ((size_t)0ULL);
v___x_3596_ = lean_usize_of_nat(v___x_3584_);
v___x_3597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3571_, v_es_3579_, v___x_3595_, v___x_3596_, v_x_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_);
lean_dec_ref(v_es_3579_);
return v___x_3597_;
}
}
else
{
size_t v___x_3598_; size_t v___x_3599_; lean_object* v___x_3600_; 
lean_del_object(v___x_3581_);
v___x_3598_ = ((size_t)0ULL);
v___x_3599_ = lean_usize_of_nat(v___x_3584_);
v___x_3600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3571_, v_es_3579_, v___x_3598_, v___x_3599_, v_x_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_);
lean_dec_ref(v_es_3579_);
return v___x_3600_;
}
}
}
}
else
{
lean_object* v_ks_3602_; lean_object* v_vs_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; 
v_ks_3602_ = lean_ctor_get(v_x_3572_, 0);
lean_inc_ref(v_ks_3602_);
v_vs_3603_ = lean_ctor_get(v_x_3572_, 1);
lean_inc_ref(v_vs_3603_);
lean_dec_ref(v_x_3572_);
v___x_3604_ = lean_unsigned_to_nat(0u);
v___x_3605_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3571_, v_ks_3602_, v_vs_3603_, v___x_3604_, v_x_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_);
lean_dec_ref(v_vs_3603_);
lean_dec_ref(v_ks_3602_);
return v___x_3605_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(lean_object* v_f_3606_, lean_object* v_as_3607_, size_t v_i_3608_, size_t v_stop_3609_, lean_object* v_b_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_){
_start:
{
lean_object* v_a_3617_; lean_object* v___y_3622_; uint8_t v___x_3625_; 
v___x_3625_ = lean_usize_dec_eq(v_i_3608_, v_stop_3609_);
if (v___x_3625_ == 0)
{
lean_object* v___x_3626_; 
v___x_3626_ = lean_array_uget_borrowed(v_as_3607_, v_i_3608_);
switch(lean_obj_tag(v___x_3626_))
{
case 0:
{
lean_object* v_key_3627_; lean_object* v_val_3628_; lean_object* v___x_3629_; 
v_key_3627_ = lean_ctor_get(v___x_3626_, 0);
v_val_3628_ = lean_ctor_get(v___x_3626_, 1);
lean_inc_ref(v_f_3606_);
lean_inc(v___y_3614_);
lean_inc_ref(v___y_3613_);
lean_inc(v___y_3612_);
lean_inc_ref(v___y_3611_);
lean_inc(v_val_3628_);
lean_inc(v_key_3627_);
v___x_3629_ = lean_apply_8(v_f_3606_, v_b_3610_, v_key_3627_, v_val_3628_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_, lean_box(0));
v___y_3622_ = v___x_3629_;
goto v___jp_3621_;
}
case 1:
{
lean_object* v_node_3630_; lean_object* v___x_3631_; 
v_node_3630_ = lean_ctor_get(v___x_3626_, 0);
lean_inc(v___y_3614_);
lean_inc_ref(v___y_3613_);
lean_inc(v___y_3612_);
lean_inc_ref(v___y_3611_);
lean_inc(v_node_3630_);
lean_inc_ref(v_f_3606_);
v___x_3631_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3606_, v_node_3630_, v_b_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
v___y_3622_ = v___x_3631_;
goto v___jp_3621_;
}
default: 
{
v_a_3617_ = v_b_3610_;
goto v___jp_3616_;
}
}
}
else
{
lean_object* v___x_3632_; lean_object* v___x_3633_; 
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec_ref(v_f_3606_);
v___x_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3632_, 0, v_b_3610_);
v___x_3633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3632_);
return v___x_3633_;
}
v___jp_3616_:
{
size_t v___x_3618_; size_t v___x_3619_; 
v___x_3618_ = ((size_t)1ULL);
v___x_3619_ = lean_usize_add(v_i_3608_, v___x_3618_);
v_i_3608_ = v___x_3619_;
v_b_3610_ = v_a_3617_;
goto _start;
}
v___jp_3621_:
{
if (lean_obj_tag(v___y_3622_) == 0)
{
lean_object* v_a_3623_; 
v_a_3623_ = lean_ctor_get(v___y_3622_, 0);
if (lean_obj_tag(v_a_3623_) == 0)
{
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec_ref(v_f_3606_);
return v___y_3622_;
}
else
{
lean_object* v_a_3624_; 
lean_inc_ref(v_a_3623_);
lean_dec_ref(v___y_3622_);
v_a_3624_ = lean_ctor_get(v_a_3623_, 0);
lean_inc(v_a_3624_);
lean_dec_ref(v_a_3623_);
v_a_3617_ = v_a_3624_;
goto v___jp_3616_;
}
}
else
{
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec_ref(v_f_3606_);
return v___y_3622_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_f_3634_, lean_object* v_as_3635_, lean_object* v_i_3636_, lean_object* v_stop_3637_, lean_object* v_b_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_){
_start:
{
size_t v_i_boxed_3644_; size_t v_stop_boxed_3645_; lean_object* v_res_3646_; 
v_i_boxed_3644_ = lean_unbox_usize(v_i_3636_);
lean_dec(v_i_3636_);
v_stop_boxed_3645_ = lean_unbox_usize(v_stop_3637_);
lean_dec(v_stop_3637_);
v_res_3646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3634_, v_as_3635_, v_i_boxed_3644_, v_stop_boxed_3645_, v_b_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_);
lean_dec_ref(v_as_3635_);
return v_res_3646_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_f_3647_, lean_object* v_x_3648_, lean_object* v_x_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_){
_start:
{
lean_object* v_res_3655_; 
v_res_3655_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3647_, v_x_3648_, v_x_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
return v_res_3655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(lean_object* v_f_3656_, lean_object* v_s_3657_, lean_object* v_a_3658_, lean_object* v_b_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_){
_start:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3665_, 0, v_a_3658_);
lean_ctor_set(v___x_3665_, 1, v_b_3659_);
v___x_3666_ = lean_apply_7(v_f_3656_, v___x_3665_, v_s_3657_, v___y_3660_, v___y_3661_, v___y_3662_, v___y_3663_, lean_box(0));
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3693_; 
v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3669_ = v___x_3666_;
v_isShared_3670_ = v_isSharedCheck_3693_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___x_3666_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3693_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
if (lean_obj_tag(v_a_3667_) == 0)
{
lean_object* v_a_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3681_; 
v_a_3671_ = lean_ctor_get(v_a_3667_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v_a_3667_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3673_ = v_a_3667_;
v_isShared_3674_ = v_isSharedCheck_3681_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_a_3671_);
lean_dec(v_a_3667_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3681_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3676_; 
if (v_isShared_3674_ == 0)
{
v___x_3676_ = v___x_3673_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_a_3671_);
v___x_3676_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
lean_object* v___x_3678_; 
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 0, v___x_3676_);
v___x_3678_ = v___x_3669_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3676_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
}
else
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3692_; 
v_a_3682_ = lean_ctor_get(v_a_3667_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v_a_3667_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3684_ = v_a_3667_;
v_isShared_3685_ = v_isSharedCheck_3692_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v_a_3667_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3692_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3687_; 
if (v_isShared_3685_ == 0)
{
v___x_3687_ = v___x_3684_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_a_3682_);
v___x_3687_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
lean_object* v___x_3689_; 
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 0, v___x_3687_);
v___x_3689_ = v___x_3669_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v___x_3687_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
}
}
}
}
else
{
lean_object* v_a_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3701_; 
v_a_3694_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3696_ = v___x_3666_;
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_a_3694_);
lean_dec(v___x_3666_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3699_; 
if (v_isShared_3697_ == 0)
{
v___x_3699_ = v___x_3696_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_a_3694_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed(lean_object* v_f_3702_, lean_object* v_s_3703_, lean_object* v_a_3704_, lean_object* v_b_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_){
_start:
{
lean_object* v_res_3711_; 
v_res_3711_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(v_f_3702_, v_s_3703_, v_a_3704_, v_b_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_);
return v_res_3711_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(lean_object* v_map_3712_, lean_object* v_init_3713_, lean_object* v_f_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
lean_object* v___f_3720_; lean_object* v___x_3721_; 
v___f_3720_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3720_, 0, v_f_3714_);
v___x_3721_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v___f_3720_, v_map_3712_, v_init_3713_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3730_; 
v_a_3722_ = lean_ctor_get(v___x_3721_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3724_ = v___x_3721_;
v_isShared_3725_ = v_isSharedCheck_3730_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_dec(v___x_3721_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3730_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v_a_3726_; lean_object* v___x_3728_; 
v_a_3726_ = lean_ctor_get(v_a_3722_, 0);
lean_inc(v_a_3726_);
lean_dec(v_a_3722_);
if (v_isShared_3725_ == 0)
{
lean_ctor_set(v___x_3724_, 0, v_a_3726_);
v___x_3728_ = v___x_3724_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_a_3726_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
else
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
v_a_3731_ = lean_ctor_get(v___x_3721_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3733_ = v___x_3721_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3721_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3736_; 
if (v_isShared_3734_ == 0)
{
v___x_3736_ = v___x_3733_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_a_3731_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
return v___x_3736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___boxed(lean_object* v_map_3739_, lean_object* v_init_3740_, lean_object* v_f_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_3739_, v_init_3740_, v_f_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(lean_object* v___y_3748_){
_start:
{
lean_object* v___x_3750_; lean_object* v_env_3751_; lean_object* v___x_3752_; lean_object* v_ext_3753_; lean_object* v_toEnvExtension_3754_; lean_object* v_asyncMode_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v_categories_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; 
v___x_3750_ = lean_st_ref_get(v___y_3748_);
v_env_3751_ = lean_ctor_get(v___x_3750_, 0);
lean_inc_ref(v_env_3751_);
lean_dec(v___x_3750_);
v___x_3752_ = l_Lean_Parser_parserExtension;
v_ext_3753_ = lean_ctor_get(v___x_3752_, 1);
lean_inc_ref(v_ext_3753_);
v_toEnvExtension_3754_ = lean_ctor_get(v_ext_3753_, 0);
lean_inc_ref(v_toEnvExtension_3754_);
lean_dec_ref(v_ext_3753_);
v_asyncMode_3755_ = lean_ctor_get(v_toEnvExtension_3754_, 2);
lean_inc(v_asyncMode_3755_);
lean_dec_ref(v_toEnvExtension_3754_);
v___x_3756_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_inc_ref(v_env_3751_);
v___x_3757_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3756_, v___x_3752_, v_env_3751_, v_asyncMode_3755_);
lean_dec(v_asyncMode_3755_);
v_categories_3758_ = lean_ctor_get(v___x_3757_, 2);
lean_inc_ref(v_categories_3758_);
lean_dec(v___x_3757_);
v___x_3759_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_3760_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_3758_, v___x_3759_);
if (lean_obj_tag(v___x_3760_) == 1)
{
lean_object* v_val_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3799_; 
v_val_3761_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3763_ = v___x_3760_;
v_isShared_3764_ = v_isSharedCheck_3799_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_val_3761_);
lean_dec(v___x_3760_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3799_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___y_3766_; lean_object* v___x_3775_; lean_object* v_toEnvExtension_3776_; lean_object* v_exportEntriesFn_3777_; lean_object* v_asyncMode_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v_importedEntries_3783_; lean_object* v___x_3784_; uint8_t v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; uint8_t v___x_3791_; 
v___x_3775_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3776_ = lean_ctor_get(v___x_3775_, 0);
lean_inc_ref(v_toEnvExtension_3776_);
v_exportEntriesFn_3777_ = lean_ctor_get(v___x_3775_, 4);
lean_inc_ref(v_exportEntriesFn_3777_);
v_asyncMode_3778_ = lean_ctor_get(v_toEnvExtension_3776_, 2);
lean_inc(v_asyncMode_3778_);
v___x_3779_ = lean_box(1);
v___x_3780_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_3781_ = lean_box(0);
lean_inc_ref(v_env_3751_);
v___x_3782_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3780_, v_toEnvExtension_3776_, v_env_3751_, v_asyncMode_3778_, v___x_3781_);
lean_dec_ref(v_toEnvExtension_3776_);
v_importedEntries_3783_ = lean_ctor_get(v___x_3782_, 0);
lean_inc_ref(v_importedEntries_3783_);
lean_dec(v___x_3782_);
lean_inc_ref(v_env_3751_);
v___x_3784_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3779_, v___x_3775_, v_env_3751_, v_asyncMode_3778_, v___x_3781_);
lean_dec(v_asyncMode_3778_);
v___x_3785_ = 0;
v___x_3786_ = lean_box(v___x_3785_);
v___x_3787_ = lean_apply_3(v_exportEntriesFn_3777_, v_env_3751_, v___x_3784_, v___x_3786_);
v___x_3788_ = lean_array_push(v_importedEntries_3783_, v___x_3787_);
v___x_3789_ = lean_unsigned_to_nat(0u);
v___x_3790_ = lean_array_get_size(v___x_3788_);
v___x_3791_ = lean_nat_dec_lt(v___x_3789_, v___x_3790_);
if (v___x_3791_ == 0)
{
lean_dec_ref(v___x_3788_);
v___y_3766_ = v___x_3779_;
goto v___jp_3765_;
}
else
{
uint8_t v___x_3792_; 
v___x_3792_ = lean_nat_dec_le(v___x_3790_, v___x_3790_);
if (v___x_3792_ == 0)
{
if (v___x_3791_ == 0)
{
lean_dec_ref(v___x_3788_);
v___y_3766_ = v___x_3779_;
goto v___jp_3765_;
}
else
{
size_t v___x_3793_; size_t v___x_3794_; lean_object* v___x_3795_; 
v___x_3793_ = ((size_t)0ULL);
v___x_3794_ = lean_usize_of_nat(v___x_3790_);
v___x_3795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3788_, v___x_3793_, v___x_3794_, v___x_3779_);
lean_dec_ref(v___x_3788_);
v___y_3766_ = v___x_3795_;
goto v___jp_3765_;
}
}
else
{
size_t v___x_3796_; size_t v___x_3797_; lean_object* v___x_3798_; 
v___x_3796_ = ((size_t)0ULL);
v___x_3797_ = lean_usize_of_nat(v___x_3790_);
v___x_3798_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3788_, v___x_3796_, v___x_3797_, v___x_3779_);
lean_dec_ref(v___x_3788_);
v___y_3766_ = v___x_3798_;
goto v___jp_3765_;
}
}
v___jp_3765_:
{
lean_object* v_tables_3767_; lean_object* v_leadingTable_3768_; lean_object* v_trailingTable_3769_; lean_object* v_firstTokens_3770_; lean_object* v_firstTokens_3771_; lean_object* v___x_3773_; 
v_tables_3767_ = lean_ctor_get(v_val_3761_, 2);
v_leadingTable_3768_ = lean_ctor_get(v_tables_3767_, 0);
v_trailingTable_3769_ = lean_ctor_get(v_tables_3767_, 2);
lean_inc(v_trailingTable_3769_);
lean_inc(v_leadingTable_3768_);
lean_inc(v_val_3761_);
v_firstTokens_3770_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_3761_, v_leadingTable_3768_, v___y_3766_);
v_firstTokens_3771_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_3761_, v_trailingTable_3769_, v_firstTokens_3770_);
if (v_isShared_3764_ == 0)
{
lean_ctor_set_tag(v___x_3763_, 0);
lean_ctor_set(v___x_3763_, 0, v_firstTokens_3771_);
v___x_3773_ = v___x_3763_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_firstTokens_3771_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
}
else
{
lean_object* v___x_3800_; lean_object* v___x_3801_; 
lean_dec(v___x_3760_);
lean_dec_ref(v_env_3751_);
v___x_3800_ = lean_box(1);
v___x_3801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3800_);
return v___x_3801_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg___boxed(lean_object* v___y_3802_, lean_object* v___y_3803_){
_start:
{
lean_object* v_res_3804_; 
v_res_3804_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_3802_);
lean_dec(v___y_3802_);
return v_res_3804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs(uint8_t v_includeUnnamed_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_){
_start:
{
lean_object* v___x_3813_; lean_object* v_env_3814_; lean_object* v___x_3815_; lean_object* v_toEnvExtension_3816_; lean_object* v_exportEntriesFn_3817_; lean_object* v_asyncMode_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v_importedEntries_3823_; lean_object* v___x_3824_; uint8_t v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; size_t v_sz_3829_; size_t v___x_3830_; lean_object* v___x_3831_; 
v___x_3813_ = lean_st_ref_get(v_a_3811_);
v_env_3814_ = lean_ctor_get(v___x_3813_, 0);
lean_inc_ref(v_env_3814_);
lean_dec(v___x_3813_);
v___x_3815_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_3816_ = lean_ctor_get(v___x_3815_, 0);
lean_inc_ref(v_toEnvExtension_3816_);
v_exportEntriesFn_3817_ = lean_ctor_get(v___x_3815_, 4);
lean_inc_ref(v_exportEntriesFn_3817_);
v_asyncMode_3818_ = lean_ctor_get(v_toEnvExtension_3816_, 2);
lean_inc(v_asyncMode_3818_);
v___x_3819_ = lean_box(1);
v___x_3820_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0);
v___x_3821_ = lean_box(0);
lean_inc_ref(v_env_3814_);
v___x_3822_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3820_, v_toEnvExtension_3816_, v_env_3814_, v_asyncMode_3818_, v___x_3821_);
lean_dec_ref(v_toEnvExtension_3816_);
v_importedEntries_3823_ = lean_ctor_get(v___x_3822_, 0);
lean_inc_ref(v_importedEntries_3823_);
lean_dec(v___x_3822_);
lean_inc_ref(v_env_3814_);
v___x_3824_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3819_, v___x_3815_, v_env_3814_, v_asyncMode_3818_, v___x_3821_);
lean_dec(v_asyncMode_3818_);
v___x_3825_ = 0;
v___x_3826_ = lean_box(v___x_3825_);
lean_inc_ref(v_env_3814_);
v___x_3827_ = lean_apply_3(v_exportEntriesFn_3817_, v_env_3814_, v___x_3824_, v___x_3826_);
v___x_3828_ = lean_array_push(v_importedEntries_3823_, v___x_3827_);
v_sz_3829_ = lean_array_size(v___x_3828_);
v___x_3830_ = ((size_t)0ULL);
v___x_3831_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v___x_3828_, v_sz_3829_, v___x_3830_, v___x_3819_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
lean_dec_ref(v___x_3828_);
if (lean_obj_tag(v___x_3831_) == 0)
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3856_; 
v_a_3832_ = lean_ctor_get(v___x_3831_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3834_ = v___x_3831_;
v_isShared_3835_ = v_isSharedCheck_3856_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3831_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3856_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3836_; lean_object* v_ext_3837_; lean_object* v_toEnvExtension_3838_; lean_object* v_asyncMode_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v_categories_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; 
v___x_3836_ = l_Lean_Parser_parserExtension;
v_ext_3837_ = lean_ctor_get(v___x_3836_, 1);
lean_inc_ref(v_ext_3837_);
v_toEnvExtension_3838_ = lean_ctor_get(v_ext_3837_, 0);
lean_inc_ref(v_toEnvExtension_3838_);
lean_dec_ref(v_ext_3837_);
v_asyncMode_3839_ = lean_ctor_get(v_toEnvExtension_3838_, 2);
lean_inc(v_asyncMode_3839_);
lean_dec_ref(v_toEnvExtension_3838_);
v___x_3840_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_inc_ref(v_env_3814_);
v___x_3841_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3840_, v___x_3836_, v_env_3814_, v_asyncMode_3839_);
lean_dec(v_asyncMode_3839_);
v_categories_3842_ = lean_ctor_get(v___x_3841_, 2);
lean_inc_ref(v_categories_3842_);
lean_dec(v___x_3841_);
v___x_3843_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0));
v___x_3844_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_3845_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_3842_, v___x_3844_);
if (lean_obj_tag(v___x_3845_) == 1)
{
lean_object* v_val_3846_; lean_object* v___x_3847_; lean_object* v_a_3848_; lean_object* v_kinds_3849_; lean_object* v___x_3850_; lean_object* v___f_3851_; lean_object* v___x_3852_; 
lean_del_object(v___x_3834_);
v_val_3846_ = lean_ctor_get(v___x_3845_, 0);
lean_inc(v_val_3846_);
lean_dec_ref(v___x_3845_);
v___x_3847_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v_a_3811_);
v_a_3848_ = lean_ctor_get(v___x_3847_, 0);
lean_inc(v_a_3848_);
lean_dec_ref(v___x_3847_);
v_kinds_3849_ = lean_ctor_get(v_val_3846_, 1);
lean_inc_ref(v_kinds_3849_);
lean_dec(v_val_3846_);
v___x_3850_ = lean_box(v_includeUnnamed_3807_);
v___f_3851_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed), 11, 4);
lean_closure_set(v___f_3851_, 0, v_env_3814_);
lean_closure_set(v___f_3851_, 1, v_a_3832_);
lean_closure_set(v___f_3851_, 2, v_a_3848_);
lean_closure_set(v___f_3851_, 3, v___x_3850_);
v___x_3852_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_kinds_3849_, v___x_3843_, v___f_3851_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
return v___x_3852_;
}
else
{
lean_object* v___x_3854_; 
lean_dec(v___x_3845_);
lean_dec(v_a_3832_);
lean_dec_ref(v_env_3814_);
lean_dec(v_a_3811_);
lean_dec_ref(v_a_3810_);
lean_dec(v_a_3809_);
lean_dec_ref(v_a_3808_);
if (v_isShared_3835_ == 0)
{
lean_ctor_set(v___x_3834_, 0, v___x_3843_);
v___x_3854_ = v___x_3834_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v___x_3843_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
}
else
{
lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3864_; 
lean_dec_ref(v_env_3814_);
lean_dec(v_a_3811_);
lean_dec_ref(v_a_3810_);
lean_dec(v_a_3809_);
lean_dec_ref(v_a_3808_);
v_a_3857_ = lean_ctor_get(v___x_3831_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3859_ = v___x_3831_;
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v___x_3831_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3862_; 
if (v_isShared_3860_ == 0)
{
v___x_3862_ = v___x_3859_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_a_3857_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
return v___x_3862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___boxed(lean_object* v_includeUnnamed_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_){
_start:
{
uint8_t v_includeUnnamed_boxed_3871_; lean_object* v_res_3872_; 
v_includeUnnamed_boxed_3871_ = lean_unbox(v_includeUnnamed_3865_);
v_res_3872_ = l_Lean_Elab_Tactic_Doc_allTacticDocs(v_includeUnnamed_boxed_3871_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(lean_object* v_as_3873_, size_t v_sz_3874_, size_t v_i_3875_, lean_object* v_b_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_){
_start:
{
lean_object* v___x_3882_; 
v___x_3882_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_3873_, v_sz_3874_, v_i_3875_, v_b_3876_);
return v___x_3882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___boxed(lean_object* v_as_3883_, lean_object* v_sz_3884_, lean_object* v_i_3885_, lean_object* v_b_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_){
_start:
{
size_t v_sz_boxed_3892_; size_t v_i_boxed_3893_; lean_object* v_res_3894_; 
v_sz_boxed_3892_ = lean_unbox_usize(v_sz_3884_);
lean_dec(v_sz_3884_);
v_i_boxed_3893_ = lean_unbox_usize(v_i_3885_);
lean_dec(v_i_3885_);
v_res_3894_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(v_as_3883_, v_sz_boxed_3892_, v_i_boxed_3893_, v_b_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
lean_dec_ref(v_as_3883_);
return v_res_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
lean_object* v___x_3900_; 
v___x_3900_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_3898_);
return v___x_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___boxed(lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_){
_start:
{
lean_object* v_res_3906_; 
v_res_3906_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_);
lean_dec(v___y_3904_);
lean_dec_ref(v___y_3903_);
lean_dec(v___y_3902_);
lean_dec_ref(v___y_3901_);
return v_res_3906_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(lean_object* v_00_u03c3_3907_, lean_object* v_00_u03b2_3908_, lean_object* v_map_3909_, lean_object* v_init_3910_, lean_object* v_f_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_){
_start:
{
lean_object* v___x_3917_; 
v___x_3917_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_3909_, v_init_3910_, v_f_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_);
return v___x_3917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___boxed(lean_object* v_00_u03c3_3918_, lean_object* v_00_u03b2_3919_, lean_object* v_map_3920_, lean_object* v_init_3921_, lean_object* v_f_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_){
_start:
{
lean_object* v_res_3928_; 
v_res_3928_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(v_00_u03c3_3918_, v_00_u03b2_3919_, v_map_3920_, v_init_3921_, v_f_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_);
return v_res_3928_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(lean_object* v_map_3929_, lean_object* v_f_3930_, lean_object* v_init_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_){
_start:
{
lean_object* v___x_3937_; 
v___x_3937_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3930_, v_map_3929_, v_init_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_);
return v___x_3937_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg___boxed(lean_object* v_map_3938_, lean_object* v_f_3939_, lean_object* v_init_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_){
_start:
{
lean_object* v_res_3946_; 
v_res_3946_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(v_map_3938_, v_f_3939_, v_init_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_);
return v_res_3946_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(lean_object* v_00_u03c3_3947_, lean_object* v_00_u03c3_3948_, lean_object* v_00_u03b2_3949_, lean_object* v_map_3950_, lean_object* v_f_3951_, lean_object* v_init_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_){
_start:
{
lean_object* v___x_3958_; 
v___x_3958_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3951_, v_map_3950_, v_init_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
return v___x_3958_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___boxed(lean_object* v_00_u03c3_3959_, lean_object* v_00_u03c3_3960_, lean_object* v_00_u03b2_3961_, lean_object* v_map_3962_, lean_object* v_f_3963_, lean_object* v_init_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_){
_start:
{
lean_object* v_res_3970_; 
v_res_3970_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(v_00_u03c3_3959_, v_00_u03c3_3960_, v_00_u03b2_3961_, v_map_3962_, v_f_3963_, v_init_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
return v_res_3970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(lean_object* v_00_u03c3_3971_, lean_object* v_00_u03c3_3972_, lean_object* v_00_u03b1_3973_, lean_object* v_00_u03b2_3974_, lean_object* v_f_3975_, lean_object* v_x_3976_, lean_object* v_x_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_){
_start:
{
lean_object* v___x_3983_; 
v___x_3983_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3975_, v_x_3976_, v_x_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_);
return v___x_3983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03c3_3984_, lean_object* v_00_u03c3_3985_, lean_object* v_00_u03b1_3986_, lean_object* v_00_u03b2_3987_, lean_object* v_f_3988_, lean_object* v_x_3989_, lean_object* v_x_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_){
_start:
{
lean_object* v_res_3996_; 
v_res_3996_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(v_00_u03c3_3984_, v_00_u03c3_3985_, v_00_u03b1_3986_, v_00_u03b2_3987_, v_f_3988_, v_x_3989_, v_x_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_);
return v_res_3996_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(lean_object* v_00_u03b1_3997_, lean_object* v_00_u03b2_3998_, lean_object* v_00_u03c3_3999_, lean_object* v_00_u03c3_4000_, lean_object* v_f_4001_, lean_object* v_as_4002_, size_t v_i_4003_, size_t v_stop_4004_, lean_object* v_b_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_){
_start:
{
lean_object* v___x_4011_; 
v___x_4011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_4001_, v_as_4002_, v_i_4003_, v_stop_4004_, v_b_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_);
return v___x_4011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b1_4012_, lean_object* v_00_u03b2_4013_, lean_object* v_00_u03c3_4014_, lean_object* v_00_u03c3_4015_, lean_object* v_f_4016_, lean_object* v_as_4017_, lean_object* v_i_4018_, lean_object* v_stop_4019_, lean_object* v_b_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_){
_start:
{
size_t v_i_boxed_4026_; size_t v_stop_boxed_4027_; lean_object* v_res_4028_; 
v_i_boxed_4026_ = lean_unbox_usize(v_i_4018_);
lean_dec(v_i_4018_);
v_stop_boxed_4027_ = lean_unbox_usize(v_stop_4019_);
lean_dec(v_stop_4019_);
v_res_4028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(v_00_u03b1_4012_, v_00_u03b2_4013_, v_00_u03c3_4014_, v_00_u03c3_4015_, v_f_4016_, v_as_4017_, v_i_boxed_4026_, v_stop_boxed_4027_, v_b_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_);
lean_dec_ref(v_as_4017_);
return v_res_4028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(lean_object* v_00_u03c3_4029_, lean_object* v_00_u03c3_4030_, lean_object* v_00_u03b1_4031_, lean_object* v_00_u03b2_4032_, lean_object* v_f_4033_, lean_object* v_keys_4034_, lean_object* v_vals_4035_, lean_object* v_heq_4036_, lean_object* v_i_4037_, lean_object* v_acc_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_){
_start:
{
lean_object* v___x_4044_; 
v___x_4044_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_4033_, v_keys_4034_, v_vals_4035_, v_i_4037_, v_acc_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_);
return v___x_4044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03c3_4045_, lean_object* v_00_u03c3_4046_, lean_object* v_00_u03b1_4047_, lean_object* v_00_u03b2_4048_, lean_object* v_f_4049_, lean_object* v_keys_4050_, lean_object* v_vals_4051_, lean_object* v_heq_4052_, lean_object* v_i_4053_, lean_object* v_acc_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_){
_start:
{
lean_object* v_res_4060_; 
v_res_4060_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(v_00_u03c3_4045_, v_00_u03c3_4046_, v_00_u03b1_4047_, v_00_u03b2_4048_, v_f_4049_, v_keys_4050_, v_vals_4051_, v_heq_4052_, v_i_4053_, v_acc_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_);
lean_dec_ref(v_vals_4051_);
lean_dec_ref(v_keys_4050_);
return v_res_4060_;
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
res = l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Doc_elabTacticExtension___regBuiltin_Lean_Elab_Tactic_Doc_elabTacticExtension_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Doc_elabRegisterTacticTag___regBuiltin_Lean_Elab_Tactic_Doc_elabRegisterTacticTag_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
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
