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
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24_spec__29___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24_spec__29___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23_spec__27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23_spec__27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__25___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__25(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24_spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___boxed(lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_198_);
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
lean_dec_ref(v___x_331_);
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
lean_dec_ref(v___x_480_);
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
lean_dec_ref(v_kind_482_);
v_str_488_ = lean_ctor_get(v_pre_483_, 1);
lean_inc_ref(v_str_488_);
lean_dec_ref(v_pre_483_);
v_str_489_ = lean_ctor_get(v_pre_484_, 1);
lean_inc_ref(v_str_489_);
lean_dec_ref(v_pre_484_);
v_str_490_ = lean_ctor_get(v_pre_485_, 1);
lean_inc_ref(v_str_490_);
lean_dec_ref(v_pre_485_);
v___x_491_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__0));
v___x_492_ = lean_string_dec_eq(v_str_490_, v___x_491_);
lean_dec_ref(v_str_490_);
if (v___x_492_ == 0)
{
lean_dec_ref(v_str_489_);
lean_dec_ref(v_str_488_);
lean_dec_ref(v_str_487_);
lean_dec_ref(v___x_480_);
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
lean_dec_ref(v___x_480_);
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
lean_dec_ref(v___x_480_);
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
lean_dec_ref(v___x_480_);
goto v___jp_465_;
}
else
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_unsigned_to_nat(0u);
v___x_500_ = l_Lean_Syntax_getArg(v___x_480_, v___x_499_);
lean_dec_ref(v___x_480_);
if (lean_obj_tag(v___x_500_) == 2)
{
lean_object* v_val_501_; 
lean_dec(v_stx_461_);
v_val_501_ = lean_ctor_get(v___x_500_, 1);
lean_inc_ref(v_val_501_);
lean_dec_ref(v___x_500_);
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
lean_dec_ref(v_pre_485_);
lean_dec_ref(v_pre_484_);
lean_dec_ref(v_pre_483_);
lean_dec_ref(v_kind_482_);
lean_dec_ref(v___x_480_);
goto v___jp_465_;
}
}
else
{
lean_dec(v_pre_485_);
lean_dec_ref(v_pre_484_);
lean_dec_ref(v_pre_483_);
lean_dec_ref(v_kind_482_);
lean_dec_ref(v___x_480_);
goto v___jp_465_;
}
}
else
{
lean_dec_ref(v_pre_483_);
lean_dec(v_pre_484_);
lean_dec_ref(v_kind_482_);
lean_dec_ref(v___x_480_);
goto v___jp_465_;
}
}
else
{
lean_dec_ref(v_kind_482_);
lean_dec(v_pre_483_);
lean_dec_ref(v___x_480_);
goto v___jp_465_;
}
}
else
{
lean_dec(v_kind_482_);
lean_dec_ref(v___x_480_);
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
v___x_533_ = lean_st_ref_take(v___y_529_);
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
v___x_551_ = l_Lean_TSyntax_getId(v___y_530_);
lean_dec(v___y_530_);
v___x_552_ = l_Lean_TSyntax_getString(v___y_531_);
lean_dec(v___y_531_);
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
v___x_559_ = lean_st_ref_set(v___y_529_, v___x_558_);
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
v___y_529_ = v___y_567_;
v___y_530_ = v_tag_569_;
v___y_531_ = v_user_575_;
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
lean_dec_ref(v___x_585_);
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
v___y_529_ = v___y_567_;
v___y_530_ = v_tag_569_;
v___y_531_ = v_user_575_;
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
lean_dec_ref(v___x_688_);
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
v___x_880_ = lean_nat_add(v___y_877_, v___y_879_);
lean_dec(v___y_879_);
lean_dec(v___y_877_);
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
lean_ctor_set(v___x_884_, 3, v___y_878_);
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
lean_ctor_set(v_reuseFailAlloc_888_, 3, v___y_878_);
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
v___y_877_ = v___x_902_;
v___y_878_ = v___x_901_;
v___y_879_ = v_size_903_;
goto v___jp_876_;
}
else
{
lean_object* v___x_904_; 
v___x_904_ = lean_unsigned_to_nat(0u);
v___y_877_ = v___x_902_;
v___y_878_ = v___x_901_;
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
lean_dec_ref(v___x_689_);
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
lean_dec_ref(v___x_1009_);
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
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1028_; size_t v___x_1029_; size_t v___x_1030_; 
v___x_1028_ = ((size_t)5ULL);
v___x_1029_ = ((size_t)1ULL);
v___x_1030_ = lean_usize_shift_left(v___x_1029_, v___x_1028_);
return v___x_1030_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1031_; size_t v___x_1032_; size_t v___x_1033_; 
v___x_1031_ = ((size_t)1ULL);
v___x_1032_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__0);
v___x_1033_ = lean_usize_sub(v___x_1032_, v___x_1031_);
return v___x_1033_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(lean_object* v_x_1034_, size_t v_x_1035_, lean_object* v_x_1036_){
_start:
{
if (lean_obj_tag(v_x_1034_) == 0)
{
lean_object* v_es_1037_; lean_object* v___x_1038_; size_t v___x_1039_; size_t v___x_1040_; size_t v___x_1041_; lean_object* v_j_1042_; lean_object* v___x_1043_; 
v_es_1037_ = lean_ctor_get(v_x_1034_, 0);
v___x_1038_ = lean_box(2);
v___x_1039_ = ((size_t)5ULL);
v___x_1040_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1);
v___x_1041_ = lean_usize_land(v_x_1035_, v___x_1040_);
v_j_1042_ = lean_usize_to_nat(v___x_1041_);
v___x_1043_ = lean_array_get_borrowed(v___x_1038_, v_es_1037_, v_j_1042_);
lean_dec(v_j_1042_);
switch(lean_obj_tag(v___x_1043_))
{
case 0:
{
lean_object* v_key_1044_; uint8_t v___x_1045_; 
v_key_1044_ = lean_ctor_get(v___x_1043_, 0);
v___x_1045_ = lean_name_eq(v_x_1036_, v_key_1044_);
return v___x_1045_;
}
case 1:
{
lean_object* v_node_1046_; size_t v___x_1047_; 
v_node_1046_ = lean_ctor_get(v___x_1043_, 0);
v___x_1047_ = lean_usize_shift_right(v_x_1035_, v___x_1039_);
v_x_1034_ = v_node_1046_;
v_x_1035_ = v___x_1047_;
goto _start;
}
default: 
{
uint8_t v___x_1049_; 
v___x_1049_ = 0;
return v___x_1049_;
}
}
}
else
{
lean_object* v_ks_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v_ks_1050_ = lean_ctor_get(v_x_1034_, 0);
v___x_1051_ = lean_unsigned_to_nat(0u);
v___x_1052_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_ks_1050_, v___x_1051_, v_x_1036_);
return v___x_1052_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___boxed(lean_object* v_x_1053_, lean_object* v_x_1054_, lean_object* v_x_1055_){
_start:
{
size_t v_x_4174__boxed_1056_; uint8_t v_res_1057_; lean_object* v_r_1058_; 
v_x_4174__boxed_1056_ = lean_unbox_usize(v_x_1054_);
lean_dec(v_x_1054_);
v_res_1057_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1053_, v_x_4174__boxed_1056_, v_x_1055_);
lean_dec(v_x_1055_);
lean_dec_ref(v_x_1053_);
v_r_1058_ = lean_box(v_res_1057_);
return v_r_1058_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1059_; uint64_t v___x_1060_; 
v___x_1059_ = lean_unsigned_to_nat(1723u);
v___x_1060_ = lean_uint64_of_nat(v___x_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(lean_object* v_x_1061_, lean_object* v_x_1062_){
_start:
{
uint64_t v___y_1064_; 
if (lean_obj_tag(v_x_1062_) == 0)
{
uint64_t v___x_1067_; 
v___x_1067_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0);
v___y_1064_ = v___x_1067_;
goto v___jp_1063_;
}
else
{
uint64_t v_hash_1068_; 
v_hash_1068_ = lean_ctor_get_uint64(v_x_1062_, sizeof(void*)*2);
v___y_1064_ = v_hash_1068_;
goto v___jp_1063_;
}
v___jp_1063_:
{
size_t v___x_1065_; uint8_t v___x_1066_; 
v___x_1065_ = lean_uint64_to_usize(v___y_1064_);
v___x_1066_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1061_, v___x_1065_, v_x_1062_);
return v___x_1066_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___boxed(lean_object* v_x_1069_, lean_object* v_x_1070_){
_start:
{
uint8_t v_res_1071_; lean_object* v_r_1072_; 
v_res_1071_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_1069_, v_x_1070_);
lean_dec(v_x_1070_);
lean_dec_ref(v_x_1069_);
v_r_1072_ = lean_box(v_res_1071_);
return v_r_1072_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(lean_object* v_tactics_1073_, lean_object* v_a_1074_, uint8_t v___x_1075_, lean_object* v_x_1076_, lean_object* v_____s_1077_){
_start:
{
lean_object* v_fst_1078_; lean_object* v_kinds_1079_; uint8_t v___x_1080_; 
v_fst_1078_ = lean_ctor_get(v_x_1076_, 0);
lean_inc(v_fst_1078_);
lean_dec_ref(v_x_1076_);
v_kinds_1079_ = lean_ctor_get(v_tactics_1073_, 1);
v___x_1080_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_kinds_1079_, v_fst_1078_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1081_; 
lean_dec(v_fst_1078_);
lean_dec(v_a_1074_);
v___x_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1081_, 0, v_____s_1077_);
return v___x_1081_;
}
else
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1082_ = l_Lean_Name_toString(v_a_1074_, v___x_1075_);
v___x_1083_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_1082_, v_fst_1078_, v_____s_1077_);
v___x_1084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
return v___x_1084_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed(lean_object* v_tactics_1085_, lean_object* v_a_1086_, lean_object* v___x_1087_, lean_object* v_x_1088_, lean_object* v_____s_1089_){
_start:
{
uint8_t v___x_4242__boxed_1090_; lean_object* v_res_1091_; 
v___x_4242__boxed_1090_ = lean_unbox(v___x_1087_);
v_res_1091_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0(v_tactics_1085_, v_a_1086_, v___x_4242__boxed_1090_, v_x_1088_, v_____s_1089_);
lean_dec_ref(v_tactics_1085_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(lean_object* v_f_1092_, lean_object* v_keys_1093_, lean_object* v_vals_1094_, lean_object* v_i_1095_, lean_object* v_acc_1096_){
_start:
{
lean_object* v___x_1097_; uint8_t v___x_1098_; 
v___x_1097_ = lean_array_get_size(v_keys_1093_);
v___x_1098_ = lean_nat_dec_lt(v_i_1095_, v___x_1097_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1099_; 
lean_dec(v_i_1095_);
lean_dec_ref(v_f_1092_);
v___x_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1099_, 0, v_acc_1096_);
return v___x_1099_;
}
else
{
lean_object* v_k_1100_; lean_object* v_v_1101_; lean_object* v___x_1102_; 
v_k_1100_ = lean_array_fget_borrowed(v_keys_1093_, v_i_1095_);
v_v_1101_ = lean_array_fget_borrowed(v_vals_1094_, v_i_1095_);
lean_inc_ref(v_f_1092_);
lean_inc(v_v_1101_);
lean_inc(v_k_1100_);
v___x_1102_ = lean_apply_3(v_f_1092_, v_acc_1096_, v_k_1100_, v_v_1101_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_dec(v_i_1095_);
lean_dec_ref(v_f_1092_);
return v___x_1102_;
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_a_1103_);
lean_dec_ref(v___x_1102_);
v___x_1104_ = lean_unsigned_to_nat(1u);
v___x_1105_ = lean_nat_add(v_i_1095_, v___x_1104_);
lean_dec(v_i_1095_);
v_i_1095_ = v___x_1105_;
v_acc_1096_ = v_a_1103_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg___boxed(lean_object* v_f_1107_, lean_object* v_keys_1108_, lean_object* v_vals_1109_, lean_object* v_i_1110_, lean_object* v_acc_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1107_, v_keys_1108_, v_vals_1109_, v_i_1110_, v_acc_1111_);
lean_dec_ref(v_vals_1109_);
lean_dec_ref(v_keys_1108_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(lean_object* v_f_1113_, lean_object* v_x_1114_, lean_object* v_x_1115_){
_start:
{
if (lean_obj_tag(v_x_1114_) == 0)
{
lean_object* v_es_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1136_; 
v_es_1116_ = lean_ctor_get(v_x_1114_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_x_1114_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1118_ = v_x_1114_;
v_isShared_1119_ = v_isSharedCheck_1136_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_es_1116_);
lean_dec(v_x_1114_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1136_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1120_ = lean_unsigned_to_nat(0u);
v___x_1121_ = lean_array_get_size(v_es_1116_);
v___x_1122_ = lean_nat_dec_lt(v___x_1120_, v___x_1121_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1124_; 
lean_dec_ref(v_es_1116_);
lean_dec_ref(v_f_1113_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set_tag(v___x_1118_, 1);
lean_ctor_set(v___x_1118_, 0, v_x_1115_);
v___x_1124_ = v___x_1118_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_x_1115_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
else
{
uint8_t v___x_1126_; 
v___x_1126_ = lean_nat_dec_le(v___x_1121_, v___x_1121_);
if (v___x_1126_ == 0)
{
if (v___x_1122_ == 0)
{
lean_object* v___x_1128_; 
lean_dec_ref(v_es_1116_);
lean_dec_ref(v_f_1113_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set_tag(v___x_1118_, 1);
lean_ctor_set(v___x_1118_, 0, v_x_1115_);
v___x_1128_ = v___x_1118_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_x_1115_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
else
{
size_t v___x_1130_; size_t v___x_1131_; lean_object* v___x_1132_; 
lean_del_object(v___x_1118_);
v___x_1130_ = ((size_t)0ULL);
v___x_1131_ = lean_usize_of_nat(v___x_1121_);
v___x_1132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1113_, v_es_1116_, v___x_1130_, v___x_1131_, v_x_1115_);
lean_dec_ref(v_es_1116_);
return v___x_1132_;
}
}
else
{
size_t v___x_1133_; size_t v___x_1134_; lean_object* v___x_1135_; 
lean_del_object(v___x_1118_);
v___x_1133_ = ((size_t)0ULL);
v___x_1134_ = lean_usize_of_nat(v___x_1121_);
v___x_1135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1113_, v_es_1116_, v___x_1133_, v___x_1134_, v_x_1115_);
lean_dec_ref(v_es_1116_);
return v___x_1135_;
}
}
}
}
else
{
lean_object* v_ks_1137_; lean_object* v_vs_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v_ks_1137_ = lean_ctor_get(v_x_1114_, 0);
lean_inc_ref(v_ks_1137_);
v_vs_1138_ = lean_ctor_get(v_x_1114_, 1);
lean_inc_ref(v_vs_1138_);
lean_dec_ref(v_x_1114_);
v___x_1139_ = lean_unsigned_to_nat(0u);
v___x_1140_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1113_, v_ks_1137_, v_vs_1138_, v___x_1139_, v_x_1115_);
lean_dec_ref(v_vs_1138_);
lean_dec_ref(v_ks_1137_);
return v___x_1140_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(lean_object* v_f_1141_, lean_object* v_as_1142_, size_t v_i_1143_, size_t v_stop_1144_, lean_object* v_b_1145_){
_start:
{
lean_object* v_a_1147_; lean_object* v___y_1152_; uint8_t v___x_1154_; 
v___x_1154_ = lean_usize_dec_eq(v_i_1143_, v_stop_1144_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; 
v___x_1155_ = lean_array_uget_borrowed(v_as_1142_, v_i_1143_);
switch(lean_obj_tag(v___x_1155_))
{
case 0:
{
lean_object* v_key_1156_; lean_object* v_val_1157_; lean_object* v___x_1158_; 
v_key_1156_ = lean_ctor_get(v___x_1155_, 0);
v_val_1157_ = lean_ctor_get(v___x_1155_, 1);
lean_inc_ref(v_f_1141_);
lean_inc(v_val_1157_);
lean_inc(v_key_1156_);
v___x_1158_ = lean_apply_3(v_f_1141_, v_b_1145_, v_key_1156_, v_val_1157_);
v___y_1152_ = v___x_1158_;
goto v___jp_1151_;
}
case 1:
{
lean_object* v_node_1159_; lean_object* v___x_1160_; 
v_node_1159_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_node_1159_);
lean_inc_ref(v_f_1141_);
v___x_1160_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1141_, v_node_1159_, v_b_1145_);
v___y_1152_ = v___x_1160_;
goto v___jp_1151_;
}
default: 
{
v_a_1147_ = v_b_1145_;
goto v___jp_1146_;
}
}
}
else
{
lean_object* v___x_1161_; 
lean_dec_ref(v_f_1141_);
v___x_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1161_, 0, v_b_1145_);
return v___x_1161_;
}
v___jp_1146_:
{
size_t v___x_1148_; size_t v___x_1149_; 
v___x_1148_ = ((size_t)1ULL);
v___x_1149_ = lean_usize_add(v_i_1143_, v___x_1148_);
v_i_1143_ = v___x_1149_;
v_b_1145_ = v_a_1147_;
goto _start;
}
v___jp_1151_:
{
if (lean_obj_tag(v___y_1152_) == 0)
{
lean_dec_ref(v_f_1141_);
return v___y_1152_;
}
else
{
lean_object* v_a_1153_; 
v_a_1153_ = lean_ctor_get(v___y_1152_, 0);
lean_inc(v_a_1153_);
lean_dec_ref(v___y_1152_);
v_a_1147_ = v_a_1153_;
goto v___jp_1146_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg___boxed(lean_object* v_f_1162_, lean_object* v_as_1163_, lean_object* v_i_1164_, lean_object* v_stop_1165_, lean_object* v_b_1166_){
_start:
{
size_t v_i_boxed_1167_; size_t v_stop_boxed_1168_; lean_object* v_res_1169_; 
v_i_boxed_1167_ = lean_unbox_usize(v_i_1164_);
lean_dec(v_i_1164_);
v_stop_boxed_1168_ = lean_unbox_usize(v_stop_1165_);
lean_dec(v_stop_1165_);
v_res_1169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1162_, v_as_1163_, v_i_boxed_1167_, v_stop_boxed_1168_, v_b_1166_);
lean_dec_ref(v_as_1163_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0(lean_object* v_f_1170_, lean_object* v_s_1171_, lean_object* v_a_1172_, lean_object* v_b_1173_){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1174_, 0, v_a_1172_);
lean_ctor_set(v___x_1174_, 1, v_b_1173_);
v___x_1175_ = lean_apply_2(v_f_1170_, v___x_1174_, v_s_1171_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1175_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1175_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
else
{
lean_object* v_a_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1191_; 
v_a_1184_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1191_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1191_ == 0)
{
v___x_1186_ = v___x_1175_;
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_a_1184_);
lean_dec(v___x_1175_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1191_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1189_; 
if (v_isShared_1187_ == 0)
{
v___x_1189_ = v___x_1186_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1190_; 
v_reuseFailAlloc_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1190_, 0, v_a_1184_);
v___x_1189_ = v_reuseFailAlloc_1190_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
return v___x_1189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(lean_object* v_map_1192_, lean_object* v_init_1193_, lean_object* v_f_1194_){
_start:
{
lean_object* v___f_1195_; lean_object* v___x_1196_; lean_object* v_a_1197_; 
v___f_1195_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1195_, 0, v_f_1194_);
lean_inc_ref(v_map_1192_);
v___x_1196_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v___f_1195_, v_map_1192_, v_init_1193_);
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_a_1197_);
lean_dec_ref(v___x_1196_);
return v_a_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg___boxed(lean_object* v_map_1198_, lean_object* v_init_1199_, lean_object* v_f_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_1198_, v_init_1199_, v_f_1200_);
lean_dec_ref(v_map_1198_);
return v_res_1201_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1202_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__0);
v___x_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(lean_object* v_tactics_1205_, lean_object* v_a_1206_, uint8_t v___x_1207_, lean_object* v_as_x27_1208_, lean_object* v_b_1209_){
_start:
{
if (lean_obj_tag(v_as_x27_1208_) == 0)
{
lean_dec(v_a_1206_);
lean_dec_ref(v_tactics_1205_);
return v_b_1209_;
}
else
{
lean_object* v_head_1210_; lean_object* v_fst_1211_; lean_object* v_info_1212_; lean_object* v_tail_1213_; lean_object* v_collectKinds_1214_; lean_object* v___x_1215_; lean_object* v___f_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v_head_1210_ = lean_ctor_get(v_as_x27_1208_, 0);
v_fst_1211_ = lean_ctor_get(v_head_1210_, 0);
v_info_1212_ = lean_ctor_get(v_fst_1211_, 0);
v_tail_1213_ = lean_ctor_get(v_as_x27_1208_, 1);
v_collectKinds_1214_ = lean_ctor_get(v_info_1212_, 1);
v___x_1215_ = lean_box(v___x_1207_);
lean_inc(v_a_1206_);
lean_inc_ref(v_tactics_1205_);
v___f_1216_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1216_, 0, v_tactics_1205_);
lean_closure_set(v___f_1216_, 1, v_a_1206_);
lean_closure_set(v___f_1216_, 2, v___x_1215_);
v___x_1217_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___closed__1);
lean_inc_ref(v_collectKinds_1214_);
v___x_1218_ = lean_apply_1(v_collectKinds_1214_, v___x_1217_);
v___x_1219_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v___x_1218_, v_b_1209_, v___f_1216_);
lean_dec_ref(v___x_1218_);
v_as_x27_1208_ = v_tail_1213_;
v_b_1209_ = v___x_1219_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg___boxed(lean_object* v_tactics_1221_, lean_object* v_a_1222_, lean_object* v___x_1223_, lean_object* v_as_x27_1224_, lean_object* v_b_1225_){
_start:
{
uint8_t v___x_4416__boxed_1226_; lean_object* v_res_1227_; 
v___x_4416__boxed_1226_ = lean_unbox(v___x_1223_);
v_res_1227_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1221_, v_a_1222_, v___x_4416__boxed_1226_, v_as_x27_1224_, v_b_1225_);
lean_dec(v_as_x27_1224_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(lean_object* v_tactics_1231_, lean_object* v_init_1232_, lean_object* v_x_1233_){
_start:
{
if (lean_obj_tag(v_x_1233_) == 0)
{
lean_object* v_k_1234_; lean_object* v_v_1235_; lean_object* v_l_1236_; lean_object* v_r_1237_; lean_object* v___x_1238_; lean_object* v_a_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; 
v_k_1234_ = lean_ctor_get(v_x_1233_, 1);
lean_inc(v_k_1234_);
v_v_1235_ = lean_ctor_get(v_x_1233_, 2);
lean_inc(v_v_1235_);
v_l_1236_ = lean_ctor_get(v_x_1233_, 3);
lean_inc(v_l_1236_);
v_r_1237_ = lean_ctor_get(v_x_1233_, 4);
lean_inc(v_r_1237_);
lean_dec_ref(v_x_1233_);
lean_inc_ref(v_tactics_1231_);
v___x_1238_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_1231_, v_init_1232_, v_l_1236_);
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
v___x_1240_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4___closed__1));
v___x_1241_ = lean_name_eq(v_k_1234_, v___x_1240_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; 
lean_dec_ref(v___x_1238_);
lean_inc_ref(v_tactics_1231_);
v___x_1242_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1231_, v_k_1234_, v___x_1241_, v_v_1235_, v_a_1239_);
lean_dec(v_v_1235_);
v_init_1232_ = v___x_1242_;
v_x_1233_ = v_r_1237_;
goto _start;
}
else
{
lean_object* v_a_1244_; 
lean_dec(v_a_1239_);
lean_dec(v_v_1235_);
lean_dec(v_k_1234_);
v_a_1244_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1244_);
lean_dec_ref(v___x_1238_);
v_init_1232_ = v_a_1244_;
v_x_1233_ = v_r_1237_;
goto _start;
}
}
else
{
lean_object* v___x_1246_; 
lean_dec_ref(v_tactics_1231_);
v___x_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1246_, 0, v_init_1232_);
return v___x_1246_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(lean_object* v_tactics_1247_, lean_object* v_table_1248_, lean_object* v_firsts_1249_){
_start:
{
lean_object* v___x_1250_; lean_object* v_a_1251_; 
v___x_1250_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__4(v_tactics_1247_, v_firsts_1249_, v_table_1248_);
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_a_1251_);
lean_dec_ref(v___x_1250_);
return v_a_1251_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(lean_object* v_00_u03b2_1252_, lean_object* v_x_1253_, lean_object* v_x_1254_){
_start:
{
uint8_t v___x_1255_; 
v___x_1255_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg(v_x_1253_, v_x_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___boxed(lean_object* v_00_u03b2_1256_, lean_object* v_x_1257_, lean_object* v_x_1258_){
_start:
{
uint8_t v_res_1259_; lean_object* v_r_1260_; 
v_res_1259_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0(v_00_u03b2_1256_, v_x_1257_, v_x_1258_);
lean_dec(v_x_1258_);
lean_dec_ref(v_x_1257_);
v_r_1260_ = lean_box(v_res_1259_);
return v_r_1260_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1(lean_object* v___x_1261_, lean_object* v_k_1262_, lean_object* v_t_1263_, lean_object* v_hl_1264_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__1___redArg(v___x_1261_, v_k_1262_, v_t_1263_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(lean_object* v_00_u03c3_1266_, lean_object* v_00_u03b2_1267_, lean_object* v_map_1268_, lean_object* v_init_1269_, lean_object* v_f_1270_){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___redArg(v_map_1268_, v_init_1269_, v_f_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2___boxed(lean_object* v_00_u03c3_1272_, lean_object* v_00_u03b2_1273_, lean_object* v_map_1274_, lean_object* v_init_1275_, lean_object* v_f_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2(v_00_u03c3_1272_, v_00_u03b2_1273_, v_map_1274_, v_init_1275_, v_f_1276_);
lean_dec_ref(v_map_1274_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(lean_object* v_tactics_1278_, lean_object* v_a_1279_, uint8_t v___x_1280_, lean_object* v_as_1281_, lean_object* v_as_x27_1282_, lean_object* v_b_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___redArg(v_tactics_1278_, v_a_1279_, v___x_1280_, v_as_x27_1282_, v_b_1283_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3___boxed(lean_object* v_tactics_1286_, lean_object* v_a_1287_, lean_object* v___x_1288_, lean_object* v_as_1289_, lean_object* v_as_x27_1290_, lean_object* v_b_1291_, lean_object* v_a_1292_){
_start:
{
uint8_t v___x_4499__boxed_1293_; lean_object* v_res_1294_; 
v___x_4499__boxed_1293_ = lean_unbox(v___x_1288_);
v_res_1294_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__3(v_tactics_1286_, v_a_1287_, v___x_4499__boxed_1293_, v_as_1289_, v_as_x27_1290_, v_b_1291_, v_a_1292_);
lean_dec(v_as_x27_1290_);
lean_dec(v_as_1289_);
return v_res_1294_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(lean_object* v_00_u03b2_1295_, lean_object* v_x_1296_, size_t v_x_1297_, lean_object* v_x_1298_){
_start:
{
uint8_t v___x_1299_; 
v___x_1299_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg(v_x_1296_, v_x_1297_, v_x_1298_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1300_, lean_object* v_x_1301_, lean_object* v_x_1302_, lean_object* v_x_1303_){
_start:
{
size_t v_x_4508__boxed_1304_; uint8_t v_res_1305_; lean_object* v_r_1306_; 
v_x_4508__boxed_1304_ = lean_unbox_usize(v_x_1302_);
lean_dec(v_x_1302_);
v_res_1305_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0(v_00_u03b2_1300_, v_x_1301_, v_x_4508__boxed_1304_, v_x_1303_);
lean_dec(v_x_1303_);
lean_dec_ref(v_x_1301_);
v_r_1306_ = lean_box(v_res_1305_);
return v_r_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3___redArg(lean_object* v_map_1307_, lean_object* v_f_1308_, lean_object* v_init_1309_){
_start:
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1308_, v_map_1307_, v_init_1309_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3(lean_object* v_00_u03c3_1311_, lean_object* v_00_u03c3_1312_, lean_object* v_00_u03b2_1313_, lean_object* v_map_1314_, lean_object* v_f_1315_, lean_object* v_init_1316_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1315_, v_map_1314_, v_init_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1318_, lean_object* v_keys_1319_, lean_object* v_vals_1320_, lean_object* v_heq_1321_, lean_object* v_i_1322_, lean_object* v_k_1323_){
_start:
{
uint8_t v___x_1324_; 
v___x_1324_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___redArg(v_keys_1319_, v_i_1322_, v_k_1323_);
return v___x_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1325_, lean_object* v_keys_1326_, lean_object* v_vals_1327_, lean_object* v_heq_1328_, lean_object* v_i_1329_, lean_object* v_k_1330_){
_start:
{
uint8_t v_res_1331_; lean_object* v_r_1332_; 
v_res_1331_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0_spec__1(v_00_u03b2_1325_, v_keys_1326_, v_vals_1327_, v_heq_1328_, v_i_1329_, v_k_1330_);
lean_dec(v_k_1330_);
lean_dec_ref(v_vals_1327_);
lean_dec_ref(v_keys_1326_);
v_r_1332_ = lean_box(v_res_1331_);
return v_r_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5(lean_object* v_00_u03c3_1333_, lean_object* v_00_u03c3_1334_, lean_object* v_00_u03b1_1335_, lean_object* v_00_u03b2_1336_, lean_object* v_f_1337_, lean_object* v_x_1338_, lean_object* v_x_1339_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5___redArg(v_f_1337_, v_x_1338_, v_x_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(lean_object* v_00_u03b1_1341_, lean_object* v_00_u03b2_1342_, lean_object* v_00_u03c3_1343_, lean_object* v_00_u03c3_1344_, lean_object* v_f_1345_, lean_object* v_as_1346_, size_t v_i_1347_, size_t v_stop_1348_, lean_object* v_b_1349_){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___redArg(v_f_1345_, v_as_1346_, v_i_1347_, v_stop_1348_, v_b_1349_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8___boxed(lean_object* v_00_u03b1_1351_, lean_object* v_00_u03b2_1352_, lean_object* v_00_u03c3_1353_, lean_object* v_00_u03c3_1354_, lean_object* v_f_1355_, lean_object* v_as_1356_, lean_object* v_i_1357_, lean_object* v_stop_1358_, lean_object* v_b_1359_){
_start:
{
size_t v_i_boxed_1360_; size_t v_stop_boxed_1361_; lean_object* v_res_1362_; 
v_i_boxed_1360_ = lean_unbox_usize(v_i_1357_);
lean_dec(v_i_1357_);
v_stop_boxed_1361_ = lean_unbox_usize(v_stop_1358_);
lean_dec(v_stop_1358_);
v_res_1362_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__8(v_00_u03b1_1351_, v_00_u03b2_1352_, v_00_u03c3_1353_, v_00_u03c3_1354_, v_f_1355_, v_as_1356_, v_i_boxed_1360_, v_stop_boxed_1361_, v_b_1359_);
lean_dec_ref(v_as_1356_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(lean_object* v_00_u03c3_1363_, lean_object* v_00_u03c3_1364_, lean_object* v_00_u03b1_1365_, lean_object* v_00_u03b2_1366_, lean_object* v_f_1367_, lean_object* v_keys_1368_, lean_object* v_vals_1369_, lean_object* v_heq_1370_, lean_object* v_i_1371_, lean_object* v_acc_1372_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___redArg(v_f_1367_, v_keys_1368_, v_vals_1369_, v_i_1371_, v_acc_1372_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9___boxed(lean_object* v_00_u03c3_1374_, lean_object* v_00_u03c3_1375_, lean_object* v_00_u03b1_1376_, lean_object* v_00_u03b2_1377_, lean_object* v_f_1378_, lean_object* v_keys_1379_, lean_object* v_vals_1380_, lean_object* v_heq_1381_, lean_object* v_i_1382_, lean_object* v_acc_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__2_spec__3_spec__5_spec__9(v_00_u03c3_1374_, v_00_u03c3_1375_, v_00_u03b1_1376_, v_00_u03b2_1377_, v_f_1378_, v_keys_1379_, v_vals_1380_, v_heq_1381_, v_i_1382_, v_acc_1383_);
lean_dec_ref(v_vals_1380_);
lean_dec_ref(v_keys_1379_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__0(lean_object* v_x1_1385_, lean_object* v_x2_1386_){
_start:
{
lean_object* v_fst_1387_; lean_object* v_snd_1388_; lean_object* v___x_1389_; 
v_fst_1387_ = lean_ctor_get(v_x2_1386_, 0);
lean_inc(v_fst_1387_);
v_snd_1388_ = lean_ctor_get(v_x2_1386_, 1);
lean_inc(v_snd_1388_);
lean_dec_ref(v_x2_1386_);
v___x_1389_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_1387_, v_snd_1388_, v_x1_1385_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1(lean_object* v___f_1409_, lean_object* v_x1_1410_, lean_object* v_x2_1411_){
_start:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; 
v___x_1412_ = lean_unsigned_to_nat(0u);
v___x_1413_ = lean_array_get_size(v_x2_1411_);
v___x_1414_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_1415_ = lean_nat_dec_lt(v___x_1412_, v___x_1413_);
if (v___x_1415_ == 0)
{
lean_dec_ref(v_x2_1411_);
lean_dec_ref(v___f_1409_);
return v_x1_1410_;
}
else
{
uint8_t v___x_1416_; 
v___x_1416_ = lean_nat_dec_le(v___x_1413_, v___x_1413_);
if (v___x_1416_ == 0)
{
if (v___x_1415_ == 0)
{
lean_dec_ref(v_x2_1411_);
lean_dec_ref(v___f_1409_);
return v_x1_1410_;
}
else
{
size_t v___x_1417_; size_t v___x_1418_; lean_object* v___x_1419_; 
v___x_1417_ = ((size_t)0ULL);
v___x_1418_ = lean_usize_of_nat(v___x_1413_);
v___x_1419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1414_, v___f_1409_, v_x2_1411_, v___x_1417_, v___x_1418_, v_x1_1410_);
return v___x_1419_;
}
}
else
{
size_t v___x_1420_; size_t v___x_1421_; lean_object* v___x_1422_; 
v___x_1420_ = ((size_t)0ULL);
v___x_1421_ = lean_usize_of_nat(v___x_1413_);
v___x_1422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1414_, v___f_1409_, v_x2_1411_, v___x_1420_, v___x_1421_, v_x1_1410_);
return v___x_1422_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(lean_object* v___x_1426_, lean_object* v___x_1427_, lean_object* v___x_1428_, lean_object* v___x_1429_, lean_object* v___x_1430_, lean_object* v_toPure_1431_, lean_object* v___f_1432_, lean_object* v_env_1433_){
_start:
{
lean_object* v___x_1434_; lean_object* v_ext_1435_; lean_object* v_toEnvExtension_1436_; lean_object* v_asyncMode_1437_; lean_object* v___x_1438_; lean_object* v_categories_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; 
v___x_1434_ = l_Lean_Parser_parserExtension;
v_ext_1435_ = lean_ctor_get(v___x_1434_, 1);
v_toEnvExtension_1436_ = lean_ctor_get(v_ext_1435_, 0);
v_asyncMode_1437_ = lean_ctor_get(v_toEnvExtension_1436_, 2);
lean_inc_ref(v_env_1433_);
v___x_1438_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1426_, v___x_1434_, v_env_1433_, v_asyncMode_1437_);
v_categories_1439_ = lean_ctor_get(v___x_1438_, 2);
lean_inc_ref(v_categories_1439_);
lean_dec(v___x_1438_);
v___x_1440_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_1441_ = l_Lean_PersistentHashMap_find_x3f___redArg(v___x_1427_, v___x_1428_, v_categories_1439_, v___x_1440_);
lean_dec_ref(v_categories_1439_);
if (lean_obj_tag(v___x_1441_) == 1)
{
lean_object* v_val_1442_; lean_object* v___y_1444_; lean_object* v___x_1451_; lean_object* v_toEnvExtension_1452_; lean_object* v_exportEntriesFn_1453_; lean_object* v_asyncMode_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v_importedEntries_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v_exported_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; uint8_t v___x_1466_; 
v_val_1442_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_val_1442_);
lean_dec_ref(v___x_1441_);
v___x_1451_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_1452_ = lean_ctor_get(v___x_1451_, 0);
v_exportEntriesFn_1453_ = lean_ctor_get(v___x_1451_, 4);
v_asyncMode_1454_ = lean_ctor_get(v_toEnvExtension_1452_, 2);
v___x_1455_ = lean_box(0);
lean_inc_ref_n(v_env_1433_, 2);
v___x_1456_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_1429_, v_toEnvExtension_1452_, v_env_1433_, v_asyncMode_1454_, v___x_1455_);
v_importedEntries_1457_ = lean_ctor_get(v___x_1456_, 0);
lean_inc_ref(v_importedEntries_1457_);
lean_dec(v___x_1456_);
v___x_1458_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1430_, v___x_1451_, v_env_1433_, v_asyncMode_1454_, v___x_1455_);
lean_inc_ref(v_exportEntriesFn_1453_);
v___x_1459_ = lean_apply_2(v_exportEntriesFn_1453_, v_env_1433_, v___x_1458_);
v_exported_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_exported_1460_);
lean_dec_ref(v___x_1459_);
v___x_1461_ = lean_box(1);
v___x_1462_ = lean_array_push(v_importedEntries_1457_, v_exported_1460_);
v___x_1463_ = lean_unsigned_to_nat(0u);
v___x_1464_ = lean_array_get_size(v___x_1462_);
v___x_1465_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v___x_1466_ = lean_nat_dec_lt(v___x_1463_, v___x_1464_);
if (v___x_1466_ == 0)
{
lean_dec_ref(v___x_1462_);
lean_dec_ref(v___f_1432_);
v___y_1444_ = v___x_1461_;
goto v___jp_1443_;
}
else
{
uint8_t v___x_1467_; 
v___x_1467_ = lean_nat_dec_le(v___x_1464_, v___x_1464_);
if (v___x_1467_ == 0)
{
if (v___x_1466_ == 0)
{
lean_dec_ref(v___x_1462_);
lean_dec_ref(v___f_1432_);
v___y_1444_ = v___x_1461_;
goto v___jp_1443_;
}
else
{
size_t v___x_1468_; size_t v___x_1469_; lean_object* v___x_1470_; 
v___x_1468_ = ((size_t)0ULL);
v___x_1469_ = lean_usize_of_nat(v___x_1464_);
v___x_1470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1465_, v___f_1432_, v___x_1462_, v___x_1468_, v___x_1469_, v___x_1461_);
v___y_1444_ = v___x_1470_;
goto v___jp_1443_;
}
}
else
{
size_t v___x_1471_; size_t v___x_1472_; lean_object* v___x_1473_; 
v___x_1471_ = ((size_t)0ULL);
v___x_1472_ = lean_usize_of_nat(v___x_1464_);
v___x_1473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1465_, v___f_1432_, v___x_1462_, v___x_1471_, v___x_1472_, v___x_1461_);
v___y_1444_ = v___x_1473_;
goto v___jp_1443_;
}
}
v___jp_1443_:
{
lean_object* v_tables_1445_; lean_object* v_leadingTable_1446_; lean_object* v_trailingTable_1447_; lean_object* v_firstTokens_1448_; lean_object* v_firstTokens_1449_; lean_object* v___x_1450_; 
v_tables_1445_ = lean_ctor_get(v_val_1442_, 2);
v_leadingTable_1446_ = lean_ctor_get(v_tables_1445_, 0);
v_trailingTable_1447_ = lean_ctor_get(v_tables_1445_, 2);
lean_inc(v_trailingTable_1447_);
lean_inc(v_leadingTable_1446_);
lean_inc(v_val_1442_);
v_firstTokens_1448_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_1442_, v_leadingTable_1446_, v___y_1444_);
v_firstTokens_1449_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_1442_, v_trailingTable_1447_, v_firstTokens_1448_);
v___x_1450_ = lean_apply_2(v_toPure_1431_, lean_box(0), v_firstTokens_1449_);
return v___x_1450_;
}
}
else
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
lean_dec(v___x_1441_);
lean_dec_ref(v_env_1433_);
lean_dec_ref(v___f_1432_);
lean_dec(v___x_1430_);
v___x_1474_ = lean_box(1);
v___x_1475_ = lean_apply_2(v_toPure_1431_, lean_box(0), v___x_1474_);
return v___x_1475_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed(lean_object* v___x_1476_, lean_object* v___x_1477_, lean_object* v___x_1478_, lean_object* v___x_1479_, lean_object* v___x_1480_, lean_object* v_toPure_1481_, lean_object* v___f_1482_, lean_object* v_env_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2(v___x_1476_, v___x_1477_, v___x_1478_, v___x_1479_, v___x_1480_, v_toPure_1481_, v___f_1482_, v_env_1483_);
lean_dec_ref(v___x_1479_);
lean_dec_ref(v___x_1476_);
return v_res_1484_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2(void){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = lean_box(1);
v___x_1489_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(lean_object* v_inst_1492_, lean_object* v_inst_1493_){
_start:
{
lean_object* v_toApplicative_1494_; lean_object* v_toBind_1495_; lean_object* v_getEnv_1496_; lean_object* v_toPure_1497_; lean_object* v___f_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___f_1504_; lean_object* v___x_1505_; 
v_toApplicative_1494_ = lean_ctor_get(v_inst_1492_, 0);
lean_inc_ref(v_toApplicative_1494_);
v_toBind_1495_ = lean_ctor_get(v_inst_1492_, 1);
lean_inc(v_toBind_1495_);
lean_dec_ref(v_inst_1492_);
v_getEnv_1496_ = lean_ctor_get(v_inst_1493_, 0);
lean_inc(v_getEnv_1496_);
lean_dec_ref(v_inst_1493_);
v_toPure_1497_ = lean_ctor_get(v_toApplicative_1494_, 1);
lean_inc(v_toPure_1497_);
lean_dec_ref(v_toApplicative_1494_);
v___f_1498_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__1));
v___x_1499_ = lean_box(1);
v___x_1500_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_1501_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_1502_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___x_1503_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___f_1504_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_1504_, 0, v___x_1503_);
lean_closure_set(v___f_1504_, 1, v___x_1501_);
lean_closure_set(v___f_1504_, 2, v___x_1502_);
lean_closure_set(v___f_1504_, 3, v___x_1500_);
lean_closure_set(v___f_1504_, 4, v___x_1499_);
lean_closure_set(v___f_1504_, 5, v_toPure_1497_);
lean_closure_set(v___f_1504_, 6, v___f_1498_);
v___x_1505_ = lean_apply_4(v_toBind_1495_, lean_box(0), lean_box(0), v_getEnv_1496_, v___f_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens(lean_object* v_m_1506_, lean_object* v_inst_1507_, lean_object* v_inst_1508_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg(v_inst_1507_, v_inst_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(lean_object* v_x_1510_, lean_object* v_y_1511_){
_start:
{
uint8_t v___x_1512_; 
v___x_1512_ = lean_nat_dec_lt(v_x_1510_, v_y_1511_);
if (v___x_1512_ == 0)
{
uint8_t v___x_1513_; 
v___x_1513_ = lean_nat_dec_eq(v_x_1510_, v_y_1511_);
if (v___x_1513_ == 0)
{
uint8_t v___x_1514_; 
v___x_1514_ = 2;
return v___x_1514_;
}
else
{
uint8_t v___x_1515_; 
v___x_1515_ = 1;
return v___x_1515_;
}
}
else
{
uint8_t v___x_1516_; 
v___x_1516_ = 0;
return v___x_1516_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0___boxed(lean_object* v_x_1517_, lean_object* v_y_1518_){
_start:
{
uint8_t v_res_1519_; lean_object* v_r_1520_; 
v_res_1519_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__0(v_x_1517_, v_y_1518_);
lean_dec(v_y_1518_);
lean_dec(v_x_1517_);
v_r_1520_ = lean_box(v_res_1519_);
return v_r_1520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__1(lean_object* v___f_1521_, lean_object* v_a_1522_, lean_object* v_x_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v_fst_1525_; lean_object* v_snd_1526_; lean_object* v_r_1527_; lean_object* v___x_1528_; 
v_fst_1525_ = lean_ctor_get(v_a_1522_, 0);
lean_inc(v_fst_1525_);
v_snd_1526_ = lean_ctor_get(v_a_1522_, 1);
lean_inc(v_snd_1526_);
lean_dec_ref(v_a_1522_);
v_r_1527_ = l_Std_DTreeMap_Internal_Impl_insert___redArg(v___f_1521_, v_fst_1525_, v_snd_1526_, v___y_1524_);
v___x_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1528_, 0, v_r_1527_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2(lean_object* v_n_1535_, lean_object* v___y_1536_, lean_object* v___f_1537_, lean_object* v_toPure_1538_, lean_object* v_firsts_1539_, lean_object* v_____do__lift_1540_){
_start:
{
lean_object* v___y_1542_; lean_object* v_val_1574_; 
if (lean_obj_tag(v_____do__lift_1540_) == 0)
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__3));
lean_inc(v_n_1535_);
v___x_1577_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___x_1576_, v_firsts_1539_, v_n_1535_);
if (lean_obj_tag(v___x_1577_) == 0)
{
uint8_t v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1578_ = 1;
lean_inc(v_n_1535_);
v___x_1579_ = l_Lean_Name_toString(v_n_1535_, v___x_1578_);
v___x_1580_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
v___y_1542_ = v___x_1580_;
goto v___jp_1541_;
}
else
{
lean_object* v_val_1581_; 
v_val_1581_ = lean_ctor_get(v___x_1577_, 0);
lean_inc(v_val_1581_);
lean_dec_ref(v___x_1577_);
v_val_1574_ = v_val_1581_;
goto v___jp_1573_;
}
}
else
{
lean_object* v_val_1582_; 
lean_dec(v_firsts_1539_);
v_val_1582_ = lean_ctor_get(v_____do__lift_1540_, 0);
lean_inc(v_val_1582_);
lean_dec_ref(v_____do__lift_1540_);
v_val_1574_ = v_val_1582_;
goto v___jp_1573_;
}
v___jp_1541_:
{
lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; uint8_t v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v_r_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1543_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__0));
v___x_1544_ = lean_unsigned_to_nat(0u);
v___x_1545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1544_);
lean_ctor_set(v___x_1545_, 1, v___y_1542_);
v___x_1546_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1543_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
v___x_1547_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
lean_ctor_set(v___x_1547_, 1, v___x_1543_);
v___x_1548_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__2));
v___x_1549_ = lean_box(2);
v___x_1550_ = 1;
lean_inc_n(v_n_1535_, 3);
v___x_1551_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1535_, v___x_1550_);
v___x_1552_ = lean_string_utf8_byte_size(v___x_1551_);
v___x_1553_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set(v___x_1553_, 1, v___x_1544_);
lean_ctor_set(v___x_1553_, 2, v___x_1552_);
v___x_1554_ = lean_box(0);
v___x_1555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1555_, 0, v_n_1535_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
lean_ctor_set(v___x_1556_, 1, v___x_1554_);
v___x_1557_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1549_);
lean_ctor_set(v___x_1557_, 1, v___x_1553_);
lean_ctor_set(v___x_1557_, 2, v_n_1535_);
lean_ctor_set(v___x_1557_, 3, v___x_1556_);
v___x_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1548_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = l_Lean_LocalContext_empty;
v___x_1560_ = lean_box(0);
v___x_1561_ = l_Lean_Expr_const___override(v_n_1535_, v___y_1536_);
v___x_1562_ = 0;
v___x_1563_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1563_, 0, v___x_1558_);
lean_ctor_set(v___x_1563_, 1, v___x_1559_);
lean_ctor_set(v___x_1563_, 2, v___x_1560_);
lean_ctor_set(v___x_1563_, 3, v___x_1561_);
lean_ctor_set_uint8(v___x_1563_, sizeof(void*)*4, v___x_1562_);
lean_ctor_set_uint8(v___x_1563_, sizeof(void*)*4 + 1, v___x_1562_);
v___x_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
v___x_1565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1544_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
v___x_1566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
lean_ctor_set(v___x_1566_, 1, v___x_1554_);
v___x_1567_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__1___closed__9));
v_r_1568_ = lean_box(1);
v___x_1569_ = l_List_forIn_x27_loop___redArg(v___x_1567_, v___f_1537_, v___x_1566_, v_r_1568_);
lean_dec_ref(v___x_1566_);
v___x_1570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1547_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
v___x_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
v___x_1572_ = lean_apply_2(v_toPure_1538_, lean_box(0), v___x_1571_);
return v___x_1572_;
}
v___jp_1573_:
{
lean_object* v___x_1575_; 
v___x_1575_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1575_, 0, v_val_1574_);
v___y_1542_ = v___x_1575_;
goto v___jp_1541_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__3(lean_object* v_n_1583_, lean_object* v___f_1584_, lean_object* v_toPure_1585_, lean_object* v_firsts_1586_, lean_object* v_inst_1587_, lean_object* v_inst_1588_, lean_object* v_toBind_1589_, lean_object* v___x_1590_, lean_object* v___x_1591_, lean_object* v___f_1592_, lean_object* v_env_1593_){
_start:
{
lean_object* v___y_1595_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1599_ = l_Lean_Environment_constants(v_env_1593_);
lean_inc(v_n_1583_);
v___x_1600_ = l_Lean_SMap_find_x3f_x27___redArg(v___x_1590_, v___x_1591_, v___x_1599_, v_n_1583_);
lean_dec_ref(v___x_1599_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v___x_1601_; 
lean_dec_ref(v___f_1592_);
v___x_1601_ = lean_box(0);
v___y_1595_ = v___x_1601_;
goto v___jp_1594_;
}
else
{
lean_object* v_val_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v_val_1602_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_val_1602_);
lean_dec_ref(v___x_1600_);
v___x_1603_ = l_Lean_ConstantInfo_levelParams(v_val_1602_);
lean_dec(v_val_1602_);
v___x_1604_ = lean_box(0);
v___x_1605_ = l_List_mapTR_loop___redArg(v___f_1592_, v___x_1603_, v___x_1604_);
v___y_1595_ = v___x_1605_;
goto v___jp_1594_;
}
v___jp_1594_:
{
lean_object* v___f_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
lean_inc(v_n_1583_);
v___f_1596_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2), 6, 5);
lean_closure_set(v___f_1596_, 0, v_n_1583_);
lean_closure_set(v___f_1596_, 1, v___y_1595_);
lean_closure_set(v___f_1596_, 2, v___f_1584_);
lean_closure_set(v___f_1596_, 3, v_toPure_1585_);
lean_closure_set(v___f_1596_, 4, v_firsts_1586_);
v___x_1597_ = l_Lean_Parser_Tactic_Doc_customTacticName___redArg(v_inst_1587_, v_inst_1588_, v_n_1583_);
v___x_1598_ = lean_apply_4(v_toBind_1589_, lean_box(0), lean_box(0), v___x_1597_, v___f_1596_);
return v___x_1598_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(lean_object* v_inst_1610_, lean_object* v_inst_1611_, lean_object* v_firsts_1612_, lean_object* v_n_1613_){
_start:
{
lean_object* v_toApplicative_1614_; lean_object* v_toBind_1615_; lean_object* v_getEnv_1616_; lean_object* v_toPure_1617_; lean_object* v___f_1618_; lean_object* v___f_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___f_1622_; lean_object* v___x_1623_; 
v_toApplicative_1614_ = lean_ctor_get(v_inst_1610_, 0);
v_toBind_1615_ = lean_ctor_get(v_inst_1610_, 1);
lean_inc_n(v_toBind_1615_, 2);
v_getEnv_1616_ = lean_ctor_get(v_inst_1611_, 0);
lean_inc(v_getEnv_1616_);
v_toPure_1617_ = lean_ctor_get(v_toApplicative_1614_, 1);
lean_inc(v_toPure_1617_);
v___f_1618_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__1));
v___f_1619_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___closed__2));
v___x_1620_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__3));
v___x_1621_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__4));
v___f_1622_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__3), 11, 10);
lean_closure_set(v___f_1622_, 0, v_n_1613_);
lean_closure_set(v___f_1622_, 1, v___f_1618_);
lean_closure_set(v___f_1622_, 2, v_toPure_1617_);
lean_closure_set(v___f_1622_, 3, v_firsts_1612_);
lean_closure_set(v___f_1622_, 4, v_inst_1610_);
lean_closure_set(v___f_1622_, 5, v_inst_1611_);
lean_closure_set(v___f_1622_, 6, v_toBind_1615_);
lean_closure_set(v___f_1622_, 7, v___x_1620_);
lean_closure_set(v___f_1622_, 8, v___x_1621_);
lean_closure_set(v___f_1622_, 9, v___f_1619_);
v___x_1623_ = lean_apply_4(v_toBind_1615_, lean_box(0), lean_box(0), v_getEnv_1616_, v___f_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName(lean_object* v_m_1624_, lean_object* v_inst_1625_, lean_object* v_inst_1626_, lean_object* v_firsts_1627_, lean_object* v_n_1628_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg(v_inst_1625_, v_inst_1626_, v_firsts_1627_, v_n_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(lean_object* v_s_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___closed__0));
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4___boxed(lean_object* v_s_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v_s_1634_);
lean_dec_ref(v_s_1634_);
return v_res_1635_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(uint8_t v___x_1636_, lean_object* v_x1_1637_, lean_object* v_x2_1638_){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; uint8_t v___x_1641_; 
v___x_1639_ = l_Lean_Name_toString(v_x1_1637_, v___x_1636_);
v___x_1640_ = l_Lean_Name_toString(v_x2_1638_, v___x_1636_);
v___x_1641_ = lean_string_dec_lt(v___x_1639_, v___x_1640_);
lean_dec_ref(v___x_1640_);
lean_dec_ref(v___x_1639_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0___boxed(lean_object* v___x_1642_, lean_object* v_x1_1643_, lean_object* v_x2_1644_){
_start:
{
uint8_t v___x_18277__boxed_1645_; uint8_t v_res_1646_; lean_object* v_r_1647_; 
v___x_18277__boxed_1645_ = lean_unbox(v___x_1642_);
v_res_1646_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_18277__boxed_1645_, v_x1_1643_, v_x2_1644_);
v_r_1647_ = lean_box(v_res_1646_);
return v_r_1647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__19___redArg(lean_object* v_hi_1648_, lean_object* v_pivot_1649_, lean_object* v_as_1650_, lean_object* v_i_1651_, lean_object* v_k_1652_){
_start:
{
uint8_t v___x_1653_; 
v___x_1653_ = lean_nat_dec_lt(v_k_1652_, v_hi_1648_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
lean_dec(v_k_1652_);
lean_dec(v_pivot_1649_);
v___x_1654_ = lean_array_fswap(v_as_1650_, v_i_1651_, v_hi_1648_);
v___x_1655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1655_, 0, v_i_1651_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
return v___x_1655_;
}
else
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; uint8_t v___x_1659_; 
v___x_1656_ = lean_array_fget_borrowed(v_as_1650_, v_k_1652_);
lean_inc(v___x_1656_);
v___x_1657_ = l_Lean_Name_toString(v___x_1656_, v___x_1653_);
lean_inc(v_pivot_1649_);
v___x_1658_ = l_Lean_Name_toString(v_pivot_1649_, v___x_1653_);
v___x_1659_ = lean_string_dec_lt(v___x_1657_, v___x_1658_);
lean_dec_ref(v___x_1658_);
lean_dec_ref(v___x_1657_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1660_ = lean_unsigned_to_nat(1u);
v___x_1661_ = lean_nat_add(v_k_1652_, v___x_1660_);
lean_dec(v_k_1652_);
v_k_1652_ = v___x_1661_;
goto _start;
}
else
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1663_ = lean_array_fswap(v_as_1650_, v_i_1651_, v_k_1652_);
v___x_1664_ = lean_unsigned_to_nat(1u);
v___x_1665_ = lean_nat_add(v_i_1651_, v___x_1664_);
lean_dec(v_i_1651_);
v___x_1666_ = lean_nat_add(v_k_1652_, v___x_1664_);
lean_dec(v_k_1652_);
v_as_1650_ = v___x_1663_;
v_i_1651_ = v___x_1665_;
v_k_1652_ = v___x_1666_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__19___redArg___boxed(lean_object* v_hi_1668_, lean_object* v_pivot_1669_, lean_object* v_as_1670_, lean_object* v_i_1671_, lean_object* v_k_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__19___redArg(v_hi_1668_, v_pivot_1669_, v_as_1670_, v_i_1671_, v_k_1672_);
lean_dec(v_hi_1668_);
return v_res_1673_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(lean_object* v_n_1674_, lean_object* v_as_1675_, lean_object* v_lo_1676_, lean_object* v_hi_1677_){
_start:
{
lean_object* v___y_1679_; uint8_t v___x_1689_; 
v___x_1689_ = lean_nat_dec_lt(v_lo_1676_, v_hi_1677_);
if (v___x_1689_ == 0)
{
lean_dec(v_lo_1676_);
return v_as_1675_;
}
else
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v_mid_1692_; lean_object* v___y_1694_; lean_object* v___y_1700_; lean_object* v___x_1705_; lean_object* v___x_1706_; uint8_t v___x_1707_; 
v___x_1690_ = lean_nat_add(v_lo_1676_, v_hi_1677_);
v___x_1691_ = lean_unsigned_to_nat(1u);
v_mid_1692_ = lean_nat_shiftr(v___x_1690_, v___x_1691_);
lean_dec(v___x_1690_);
v___x_1705_ = lean_array_fget_borrowed(v_as_1675_, v_mid_1692_);
v___x_1706_ = lean_array_fget_borrowed(v_as_1675_, v_lo_1676_);
lean_inc(v___x_1706_);
lean_inc(v___x_1705_);
v___x_1707_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_1689_, v___x_1705_, v___x_1706_);
if (v___x_1707_ == 0)
{
v___y_1700_ = v_as_1675_;
goto v___jp_1699_;
}
else
{
lean_object* v___x_1708_; 
v___x_1708_ = lean_array_fswap(v_as_1675_, v_lo_1676_, v_mid_1692_);
v___y_1700_ = v___x_1708_;
goto v___jp_1699_;
}
v___jp_1693_:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; uint8_t v___x_1697_; 
v___x_1695_ = lean_array_fget_borrowed(v___y_1694_, v_mid_1692_);
v___x_1696_ = lean_array_fget_borrowed(v___y_1694_, v_hi_1677_);
lean_inc(v___x_1696_);
lean_inc(v___x_1695_);
v___x_1697_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_1689_, v___x_1695_, v___x_1696_);
if (v___x_1697_ == 0)
{
lean_dec(v_mid_1692_);
v___y_1679_ = v___y_1694_;
goto v___jp_1678_;
}
else
{
lean_object* v___x_1698_; 
v___x_1698_ = lean_array_fswap(v___y_1694_, v_mid_1692_, v_hi_1677_);
lean_dec(v_mid_1692_);
v___y_1679_ = v___x_1698_;
goto v___jp_1678_;
}
}
v___jp_1699_:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; uint8_t v___x_1703_; 
v___x_1701_ = lean_array_fget_borrowed(v___y_1700_, v_hi_1677_);
v___x_1702_ = lean_array_fget_borrowed(v___y_1700_, v_lo_1676_);
lean_inc(v___x_1702_);
lean_inc(v___x_1701_);
v___x_1703_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___lam__0(v___x_1689_, v___x_1701_, v___x_1702_);
if (v___x_1703_ == 0)
{
v___y_1694_ = v___y_1700_;
goto v___jp_1693_;
}
else
{
lean_object* v___x_1704_; 
v___x_1704_ = lean_array_fswap(v___y_1700_, v_lo_1676_, v_hi_1677_);
v___y_1694_ = v___x_1704_;
goto v___jp_1693_;
}
}
}
v___jp_1678_:
{
lean_object* v_pivot_1680_; lean_object* v___x_1681_; lean_object* v_fst_1682_; lean_object* v_snd_1683_; uint8_t v___x_1684_; 
v_pivot_1680_ = lean_array_fget(v___y_1679_, v_hi_1677_);
lean_inc_n(v_lo_1676_, 2);
v___x_1681_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__19___redArg(v_hi_1677_, v_pivot_1680_, v___y_1679_, v_lo_1676_, v_lo_1676_);
v_fst_1682_ = lean_ctor_get(v___x_1681_, 0);
lean_inc(v_fst_1682_);
v_snd_1683_ = lean_ctor_get(v___x_1681_, 1);
lean_inc(v_snd_1683_);
lean_dec_ref(v___x_1681_);
v___x_1684_ = lean_nat_dec_le(v_hi_1677_, v_fst_1682_);
if (v___x_1684_ == 0)
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_1674_, v_snd_1683_, v_lo_1676_, v_fst_1682_);
v___x_1686_ = lean_unsigned_to_nat(1u);
v___x_1687_ = lean_nat_add(v_fst_1682_, v___x_1686_);
lean_dec(v_fst_1682_);
v_as_1675_ = v___x_1685_;
v_lo_1676_ = v___x_1687_;
goto _start;
}
else
{
lean_dec(v_fst_1682_);
lean_dec(v_lo_1676_);
return v_snd_1683_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg___boxed(lean_object* v_n_1709_, lean_object* v_as_1710_, lean_object* v_lo_1711_, lean_object* v_hi_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_1709_, v_as_1710_, v_lo_1711_, v_hi_1712_);
lean_dec(v_hi_1712_);
lean_dec(v_n_1709_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___redArg(lean_object* v_a_1714_, lean_object* v_x_1715_){
_start:
{
if (lean_obj_tag(v_x_1715_) == 0)
{
lean_object* v___x_1716_; 
v___x_1716_ = lean_box(0);
return v___x_1716_;
}
else
{
lean_object* v_key_1717_; lean_object* v_value_1718_; lean_object* v_tail_1719_; uint8_t v___x_1720_; 
v_key_1717_ = lean_ctor_get(v_x_1715_, 0);
v_value_1718_ = lean_ctor_get(v_x_1715_, 1);
v_tail_1719_ = lean_ctor_get(v_x_1715_, 2);
v___x_1720_ = lean_name_eq(v_key_1717_, v_a_1714_);
if (v___x_1720_ == 0)
{
v_x_1715_ = v_tail_1719_;
goto _start;
}
else
{
lean_object* v___x_1722_; 
lean_inc(v_value_1718_);
v___x_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1722_, 0, v_value_1718_);
return v___x_1722_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___redArg___boxed(lean_object* v_a_1723_, lean_object* v_x_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___redArg(v_a_1723_, v_x_1724_);
lean_dec(v_x_1724_);
lean_dec(v_a_1723_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg(lean_object* v_m_1726_, lean_object* v_a_1727_){
_start:
{
lean_object* v_buckets_1728_; lean_object* v___x_1729_; uint64_t v___y_1731_; 
v_buckets_1728_ = lean_ctor_get(v_m_1726_, 1);
v___x_1729_ = lean_array_get_size(v_buckets_1728_);
if (lean_obj_tag(v_a_1727_) == 0)
{
uint64_t v___x_1745_; 
v___x_1745_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0);
v___y_1731_ = v___x_1745_;
goto v___jp_1730_;
}
else
{
uint64_t v_hash_1746_; 
v_hash_1746_ = lean_ctor_get_uint64(v_a_1727_, sizeof(void*)*2);
v___y_1731_ = v_hash_1746_;
goto v___jp_1730_;
}
v___jp_1730_:
{
uint64_t v___x_1732_; uint64_t v___x_1733_; uint64_t v_fold_1734_; uint64_t v___x_1735_; uint64_t v___x_1736_; uint64_t v___x_1737_; size_t v___x_1738_; size_t v___x_1739_; size_t v___x_1740_; size_t v___x_1741_; size_t v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1732_ = 32ULL;
v___x_1733_ = lean_uint64_shift_right(v___y_1731_, v___x_1732_);
v_fold_1734_ = lean_uint64_xor(v___y_1731_, v___x_1733_);
v___x_1735_ = 16ULL;
v___x_1736_ = lean_uint64_shift_right(v_fold_1734_, v___x_1735_);
v___x_1737_ = lean_uint64_xor(v_fold_1734_, v___x_1736_);
v___x_1738_ = lean_uint64_to_usize(v___x_1737_);
v___x_1739_ = lean_usize_of_nat(v___x_1729_);
v___x_1740_ = ((size_t)1ULL);
v___x_1741_ = lean_usize_sub(v___x_1739_, v___x_1740_);
v___x_1742_ = lean_usize_land(v___x_1738_, v___x_1741_);
v___x_1743_ = lean_array_uget_borrowed(v_buckets_1728_, v___x_1742_);
v___x_1744_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___redArg(v_a_1727_, v___x_1743_);
return v___x_1744_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg___boxed(lean_object* v_m_1747_, lean_object* v_a_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg(v_m_1747_, v_a_1748_);
lean_dec(v_a_1748_);
lean_dec_ref(v_m_1747_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(lean_object* v_keys_1750_, lean_object* v_vals_1751_, lean_object* v_i_1752_, lean_object* v_k_1753_){
_start:
{
lean_object* v___x_1754_; uint8_t v___x_1755_; 
v___x_1754_ = lean_array_get_size(v_keys_1750_);
v___x_1755_ = lean_nat_dec_lt(v_i_1752_, v___x_1754_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; 
lean_dec(v_i_1752_);
v___x_1756_ = lean_box(0);
return v___x_1756_;
}
else
{
lean_object* v_k_x27_1757_; uint8_t v___x_1758_; 
v_k_x27_1757_ = lean_array_fget_borrowed(v_keys_1750_, v_i_1752_);
v___x_1758_ = lean_name_eq(v_k_1753_, v_k_x27_1757_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = lean_unsigned_to_nat(1u);
v___x_1760_ = lean_nat_add(v_i_1752_, v___x_1759_);
lean_dec(v_i_1752_);
v_i_1752_ = v___x_1760_;
goto _start;
}
else
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = lean_array_fget_borrowed(v_vals_1751_, v_i_1752_);
lean_dec(v_i_1752_);
lean_inc(v___x_1762_);
v___x_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
return v___x_1763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg___boxed(lean_object* v_keys_1764_, lean_object* v_vals_1765_, lean_object* v_i_1766_, lean_object* v_k_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_1764_, v_vals_1765_, v_i_1766_, v_k_1767_);
lean_dec(v_k_1767_);
lean_dec_ref(v_vals_1765_);
lean_dec_ref(v_keys_1764_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(lean_object* v_x_1769_, size_t v_x_1770_, lean_object* v_x_1771_){
_start:
{
if (lean_obj_tag(v_x_1769_) == 0)
{
lean_object* v_es_1772_; lean_object* v___x_1773_; size_t v___x_1774_; size_t v___x_1775_; size_t v___x_1776_; lean_object* v_j_1777_; lean_object* v___x_1778_; 
v_es_1772_ = lean_ctor_get(v_x_1769_, 0);
v___x_1773_ = lean_box(2);
v___x_1774_ = ((size_t)5ULL);
v___x_1775_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0_spec__0___redArg___closed__1);
v___x_1776_ = lean_usize_land(v_x_1770_, v___x_1775_);
v_j_1777_ = lean_usize_to_nat(v___x_1776_);
v___x_1778_ = lean_array_get_borrowed(v___x_1773_, v_es_1772_, v_j_1777_);
lean_dec(v_j_1777_);
switch(lean_obj_tag(v___x_1778_))
{
case 0:
{
lean_object* v_key_1779_; lean_object* v_val_1780_; uint8_t v___x_1781_; 
v_key_1779_ = lean_ctor_get(v___x_1778_, 0);
v_val_1780_ = lean_ctor_get(v___x_1778_, 1);
v___x_1781_ = lean_name_eq(v_x_1771_, v_key_1779_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1782_; 
v___x_1782_ = lean_box(0);
return v___x_1782_;
}
else
{
lean_object* v___x_1783_; 
lean_inc(v_val_1780_);
v___x_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1783_, 0, v_val_1780_);
return v___x_1783_;
}
}
case 1:
{
lean_object* v_node_1784_; size_t v___x_1785_; 
v_node_1784_ = lean_ctor_get(v___x_1778_, 0);
v___x_1785_ = lean_usize_shift_right(v_x_1770_, v___x_1774_);
v_x_1769_ = v_node_1784_;
v_x_1770_ = v___x_1785_;
goto _start;
}
default: 
{
lean_object* v___x_1787_; 
v___x_1787_ = lean_box(0);
return v___x_1787_;
}
}
}
else
{
lean_object* v_ks_1788_; lean_object* v_vs_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v_ks_1788_ = lean_ctor_get(v_x_1769_, 0);
v_vs_1789_ = lean_ctor_get(v_x_1769_, 1);
v___x_1790_ = lean_unsigned_to_nat(0u);
v___x_1791_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_ks_1788_, v_vs_1789_, v___x_1790_, v_x_1771_);
return v___x_1791_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_x_1792_, lean_object* v_x_1793_, lean_object* v_x_1794_){
_start:
{
size_t v_x_18460__boxed_1795_; lean_object* v_res_1796_; 
v_x_18460__boxed_1795_ = lean_unbox_usize(v_x_1793_);
lean_dec(v_x_1793_);
v_res_1796_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_1792_, v_x_18460__boxed_1795_, v_x_1794_);
lean_dec(v_x_1794_);
lean_dec_ref(v_x_1792_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(lean_object* v_x_1797_, lean_object* v_x_1798_){
_start:
{
uint64_t v___y_1800_; 
if (lean_obj_tag(v_x_1798_) == 0)
{
uint64_t v___x_1803_; 
v___x_1803_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens_spec__0___redArg___closed__0);
v___y_1800_ = v___x_1803_;
goto v___jp_1799_;
}
else
{
uint64_t v_hash_1804_; 
v_hash_1804_ = lean_ctor_get_uint64(v_x_1798_, sizeof(void*)*2);
v___y_1800_ = v_hash_1804_;
goto v___jp_1799_;
}
v___jp_1799_:
{
size_t v___x_1801_; lean_object* v___x_1802_; 
v___x_1801_ = lean_uint64_to_usize(v___y_1800_);
v___x_1802_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_1797_, v___x_1801_, v_x_1798_);
return v___x_1802_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg___boxed(lean_object* v_x_1805_, lean_object* v_x_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_1805_, v_x_1806_);
lean_dec(v_x_1806_);
lean_dec_ref(v_x_1805_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___redArg(lean_object* v_x_1808_, lean_object* v_x_1809_){
_start:
{
uint8_t v_stage_u2081_1810_; 
v_stage_u2081_1810_ = lean_ctor_get_uint8(v_x_1808_, sizeof(void*)*2);
if (v_stage_u2081_1810_ == 0)
{
lean_object* v_map_u2081_1811_; lean_object* v_map_u2082_1812_; lean_object* v___x_1813_; 
v_map_u2081_1811_ = lean_ctor_get(v_x_1808_, 0);
v_map_u2082_1812_ = lean_ctor_get(v_x_1808_, 1);
v___x_1813_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg(v_map_u2081_1811_, v_x_1809_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v___x_1814_; 
v___x_1814_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_map_u2082_1812_, v_x_1809_);
return v___x_1814_;
}
else
{
return v___x_1813_;
}
}
else
{
lean_object* v_map_u2081_1815_; lean_object* v___x_1816_; 
v_map_u2081_1815_ = lean_ctor_get(v_x_1808_, 0);
v___x_1816_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg(v_map_u2081_1815_, v_x_1809_);
return v___x_1816_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___redArg___boxed(lean_object* v_x_1817_, lean_object* v_x_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___redArg(v_x_1817_, v_x_1818_);
lean_dec(v_x_1818_);
lean_dec_ref(v_x_1817_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__14(lean_object* v_a_1820_, lean_object* v_a_1821_){
_start:
{
if (lean_obj_tag(v_a_1820_) == 0)
{
lean_object* v___x_1822_; 
v___x_1822_ = l_List_reverse___redArg(v_a_1821_);
return v___x_1822_;
}
else
{
lean_object* v_head_1823_; lean_object* v_tail_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1833_; 
v_head_1823_ = lean_ctor_get(v_a_1820_, 0);
v_tail_1824_ = lean_ctor_get(v_a_1820_, 1);
v_isSharedCheck_1833_ = !lean_is_exclusive(v_a_1820_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1826_ = v_a_1820_;
v_isShared_1827_ = v_isSharedCheck_1833_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_tail_1824_);
lean_inc(v_head_1823_);
lean_dec(v_a_1820_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1833_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1828_; lean_object* v___x_1830_; 
v___x_1828_ = l_Lean_Level_param___override(v_head_1823_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 1, v_a_1821_);
lean_ctor_set(v___x_1826_, 0, v___x_1828_);
v___x_1830_ = v___x_1826_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1828_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v_a_1821_);
v___x_1830_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
v_a_1820_ = v_tail_1824_;
v_a_1821_ = v___x_1830_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg(lean_object* v_t_1834_, lean_object* v_k_1835_){
_start:
{
if (lean_obj_tag(v_t_1834_) == 0)
{
lean_object* v_k_1836_; lean_object* v_v_1837_; lean_object* v_l_1838_; lean_object* v_r_1839_; uint8_t v___x_1840_; 
v_k_1836_ = lean_ctor_get(v_t_1834_, 1);
v_v_1837_ = lean_ctor_get(v_t_1834_, 2);
v_l_1838_ = lean_ctor_get(v_t_1834_, 3);
v_r_1839_ = lean_ctor_get(v_t_1834_, 4);
v___x_1840_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1835_, v_k_1836_);
switch(v___x_1840_)
{
case 0:
{
v_t_1834_ = v_l_1838_;
goto _start;
}
case 1:
{
lean_object* v___x_1842_; 
lean_inc(v_v_1837_);
v___x_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1842_, 0, v_v_1837_);
return v___x_1842_;
}
default: 
{
v_t_1834_ = v_r_1839_;
goto _start;
}
}
}
else
{
lean_object* v___x_1844_; 
v___x_1844_ = lean_box(0);
return v___x_1844_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg___boxed(lean_object* v_t_1845_, lean_object* v_k_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg(v_t_1845_, v_k_1846_);
lean_dec(v_k_1846_);
lean_dec(v_t_1845_);
return v_res_1847_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(lean_object* v_x1_1848_, lean_object* v_x2_1849_){
_start:
{
lean_object* v_fst_1850_; lean_object* v_fst_1851_; uint8_t v___x_1852_; 
v_fst_1850_ = lean_ctor_get(v_x1_1848_, 0);
v_fst_1851_ = lean_ctor_get(v_x2_1849_, 0);
v___x_1852_ = l_Lean_Name_quickLt(v_fst_1850_, v_fst_1851_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0___boxed(lean_object* v_x1_1853_, lean_object* v_x2_1854_){
_start:
{
uint8_t v_res_1855_; lean_object* v_r_1856_; 
v_res_1855_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_x1_1853_, v_x2_1854_);
lean_dec_ref(v_x2_1854_);
lean_dec_ref(v_x1_1853_);
v_r_1856_ = lean_box(v_res_1855_);
return v_r_1856_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(lean_object* v_as_1857_, lean_object* v_k_1858_, lean_object* v_x_1859_, lean_object* v_x_1860_){
_start:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v_m_1863_; lean_object* v_a_1864_; uint8_t v___x_1865_; 
v___x_1861_ = lean_nat_add(v_x_1859_, v_x_1860_);
v___x_1862_ = lean_unsigned_to_nat(1u);
v_m_1863_ = lean_nat_shiftr(v___x_1861_, v___x_1862_);
lean_dec(v___x_1861_);
v_a_1864_ = lean_array_fget_borrowed(v_as_1857_, v_m_1863_);
v___x_1865_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_a_1864_, v_k_1858_);
if (v___x_1865_ == 0)
{
uint8_t v___x_1866_; 
lean_dec(v_x_1860_);
v___x_1866_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___lam__0(v_k_1858_, v_a_1864_);
if (v___x_1866_ == 0)
{
lean_object* v___x_1867_; 
lean_dec(v_m_1863_);
lean_dec(v_x_1859_);
lean_inc(v_a_1864_);
v___x_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1867_, 0, v_a_1864_);
return v___x_1867_;
}
else
{
lean_object* v___x_1868_; uint8_t v___x_1869_; 
v___x_1868_ = lean_unsigned_to_nat(0u);
v___x_1869_ = lean_nat_dec_eq(v_m_1863_, v___x_1868_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1870_; uint8_t v___x_1871_; 
v___x_1870_ = lean_nat_sub(v_m_1863_, v___x_1862_);
lean_dec(v_m_1863_);
v___x_1871_ = lean_nat_dec_lt(v___x_1870_, v_x_1859_);
if (v___x_1871_ == 0)
{
v_x_1860_ = v___x_1870_;
goto _start;
}
else
{
lean_object* v___x_1873_; 
lean_dec(v___x_1870_);
lean_dec(v_x_1859_);
v___x_1873_ = lean_box(0);
return v___x_1873_;
}
}
else
{
lean_object* v___x_1874_; 
lean_dec(v_m_1863_);
lean_dec(v_x_1859_);
v___x_1874_ = lean_box(0);
return v___x_1874_;
}
}
}
else
{
lean_object* v___x_1875_; uint8_t v___x_1876_; 
lean_dec(v_x_1859_);
v___x_1875_ = lean_nat_add(v_m_1863_, v___x_1862_);
lean_dec(v_m_1863_);
v___x_1876_ = lean_nat_dec_le(v___x_1875_, v_x_1860_);
if (v___x_1876_ == 0)
{
lean_object* v___x_1877_; 
lean_dec(v___x_1875_);
lean_dec(v_x_1860_);
v___x_1877_ = lean_box(0);
return v___x_1877_;
}
else
{
v_x_1859_ = v___x_1875_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg___boxed(lean_object* v_as_1879_, lean_object* v_k_1880_, lean_object* v_x_1881_, lean_object* v_x_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_1879_, v_k_1880_, v_x_1881_, v_x_1882_);
lean_dec_ref(v_k_1880_);
lean_dec_ref(v_as_1879_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(lean_object* v_tac_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v___x_1888_; lean_object* v_env_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1888_ = lean_st_ref_get(v___y_1886_);
v_env_1892_ = lean_ctor_get(v___x_1888_, 0);
lean_inc_ref(v_env_1892_);
lean_dec(v___x_1888_);
v___x_1893_ = lean_box(1);
v___x_1894_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1892_, v_tac_1885_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v___x_1895_; lean_object* v_toEnvExtension_1896_; lean_object* v_asyncMode_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1895_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_1896_ = lean_ctor_get(v___x_1895_, 0);
v_asyncMode_1897_ = lean_ctor_get(v_toEnvExtension_1896_, 2);
v___x_1898_ = lean_box(0);
v___x_1899_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_1893_, v___x_1895_, v_env_1892_, v_asyncMode_1897_, v___x_1898_);
v___x_1900_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1899_, v_tac_1885_);
lean_dec(v_tac_1885_);
lean_dec(v___x_1899_);
v___x_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
return v___x_1901_;
}
else
{
lean_object* v_val_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1930_; 
v_val_1902_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1904_ = v___x_1894_;
v_isShared_1905_ = v_isSharedCheck_1930_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_val_1902_);
lean_dec(v___x_1894_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1930_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1906_; uint8_t v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; uint8_t v___x_1911_; 
v___x_1906_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v___x_1907_ = 0;
v___x_1908_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_1893_, v___x_1906_, v_env_1892_, v_val_1902_, v___x_1907_);
lean_dec(v_val_1902_);
lean_dec_ref(v_env_1892_);
v___x_1909_ = lean_unsigned_to_nat(0u);
v___x_1910_ = lean_array_get_size(v___x_1908_);
v___x_1911_ = lean_nat_dec_lt(v___x_1909_, v___x_1910_);
if (v___x_1911_ == 0)
{
lean_dec_ref(v___x_1908_);
lean_del_object(v___x_1904_);
lean_dec(v_tac_1885_);
goto v___jp_1889_;
}
else
{
lean_object* v___x_1912_; lean_object* v___x_1913_; uint8_t v___x_1914_; 
v___x_1912_ = lean_unsigned_to_nat(1u);
v___x_1913_ = lean_nat_sub(v___x_1910_, v___x_1912_);
v___x_1914_ = lean_nat_dec_le(v___x_1909_, v___x_1913_);
if (v___x_1914_ == 0)
{
lean_dec(v___x_1913_);
lean_dec_ref(v___x_1908_);
lean_del_object(v___x_1904_);
lean_dec(v_tac_1885_);
goto v___jp_1889_;
}
else
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1915_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0));
v___x_1916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1916_, 0, v_tac_1885_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v___x_1908_, v___x_1916_, v___x_1909_, v___x_1913_);
lean_dec_ref(v___x_1916_);
lean_dec_ref(v___x_1908_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_del_object(v___x_1904_);
goto v___jp_1889_;
}
else
{
lean_object* v_val_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1929_; 
v_val_1918_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1920_ = v___x_1917_;
v_isShared_1921_ = v_isSharedCheck_1929_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_val_1918_);
lean_dec(v___x_1917_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1929_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v_snd_1922_; lean_object* v___x_1924_; 
v_snd_1922_ = lean_ctor_get(v_val_1918_, 1);
lean_inc(v_snd_1922_);
lean_dec(v_val_1918_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 0, v_snd_1922_);
v___x_1924_ = v___x_1920_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_snd_1922_);
v___x_1924_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
lean_object* v___x_1926_; 
if (v_isShared_1905_ == 0)
{
lean_ctor_set_tag(v___x_1904_, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1924_);
v___x_1926_ = v___x_1904_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1924_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
}
}
}
}
v___jp_1889_:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = lean_box(0);
v___x_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
return v___x_1891_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___boxed(lean_object* v_tac_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_1931_, v___y_1932_);
lean_dec(v___y_1932_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(lean_object* v_k_1935_, lean_object* v_v_1936_, lean_object* v_t_1937_){
_start:
{
if (lean_obj_tag(v_t_1937_) == 0)
{
lean_object* v_size_1938_; lean_object* v_k_1939_; lean_object* v_v_1940_; lean_object* v_l_1941_; lean_object* v_r_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_2223_; 
v_size_1938_ = lean_ctor_get(v_t_1937_, 0);
v_k_1939_ = lean_ctor_get(v_t_1937_, 1);
v_v_1940_ = lean_ctor_get(v_t_1937_, 2);
v_l_1941_ = lean_ctor_get(v_t_1937_, 3);
v_r_1942_ = lean_ctor_get(v_t_1937_, 4);
v_isSharedCheck_2223_ = !lean_is_exclusive(v_t_1937_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_1944_ = v_t_1937_;
v_isShared_1945_ = v_isSharedCheck_2223_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_r_1942_);
lean_inc(v_l_1941_);
lean_inc(v_v_1940_);
lean_inc(v_k_1939_);
lean_inc(v_size_1938_);
lean_dec(v_t_1937_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_2223_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
uint8_t v___x_1946_; 
v___x_1946_ = lean_nat_dec_lt(v_k_1935_, v_k_1939_);
if (v___x_1946_ == 0)
{
uint8_t v___x_1947_; 
v___x_1947_ = lean_nat_dec_eq(v_k_1935_, v_k_1939_);
if (v___x_1947_ == 0)
{
lean_object* v_impl_1948_; lean_object* v___x_1949_; 
lean_dec(v_size_1938_);
v_impl_1948_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_k_1935_, v_v_1936_, v_r_1942_);
v___x_1949_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1941_) == 0)
{
lean_object* v_size_1950_; lean_object* v_size_1951_; lean_object* v_k_1952_; lean_object* v_v_1953_; lean_object* v_l_1954_; lean_object* v_r_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; 
v_size_1950_ = lean_ctor_get(v_l_1941_, 0);
v_size_1951_ = lean_ctor_get(v_impl_1948_, 0);
lean_inc(v_size_1951_);
v_k_1952_ = lean_ctor_get(v_impl_1948_, 1);
lean_inc(v_k_1952_);
v_v_1953_ = lean_ctor_get(v_impl_1948_, 2);
lean_inc(v_v_1953_);
v_l_1954_ = lean_ctor_get(v_impl_1948_, 3);
lean_inc(v_l_1954_);
v_r_1955_ = lean_ctor_get(v_impl_1948_, 4);
lean_inc(v_r_1955_);
v___x_1956_ = lean_unsigned_to_nat(3u);
v___x_1957_ = lean_nat_mul(v___x_1956_, v_size_1950_);
v___x_1958_ = lean_nat_dec_lt(v___x_1957_, v_size_1951_);
lean_dec(v___x_1957_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1962_; 
lean_dec(v_r_1955_);
lean_dec(v_l_1954_);
lean_dec(v_v_1953_);
lean_dec(v_k_1952_);
v___x_1959_ = lean_nat_add(v___x_1949_, v_size_1950_);
v___x_1960_ = lean_nat_add(v___x_1959_, v_size_1951_);
lean_dec(v_size_1951_);
lean_dec(v___x_1959_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v_impl_1948_);
lean_ctor_set(v___x_1944_, 0, v___x_1960_);
v___x_1962_ = v___x_1944_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1960_);
lean_ctor_set(v_reuseFailAlloc_1963_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_1963_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_1963_, 3, v_l_1941_);
lean_ctor_set(v_reuseFailAlloc_1963_, 4, v_impl_1948_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
else
{
lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_2027_; 
v_isSharedCheck_2027_ = !lean_is_exclusive(v_impl_1948_);
if (v_isSharedCheck_2027_ == 0)
{
lean_object* v_unused_2028_; lean_object* v_unused_2029_; lean_object* v_unused_2030_; lean_object* v_unused_2031_; lean_object* v_unused_2032_; 
v_unused_2028_ = lean_ctor_get(v_impl_1948_, 4);
lean_dec(v_unused_2028_);
v_unused_2029_ = lean_ctor_get(v_impl_1948_, 3);
lean_dec(v_unused_2029_);
v_unused_2030_ = lean_ctor_get(v_impl_1948_, 2);
lean_dec(v_unused_2030_);
v_unused_2031_ = lean_ctor_get(v_impl_1948_, 1);
lean_dec(v_unused_2031_);
v_unused_2032_ = lean_ctor_get(v_impl_1948_, 0);
lean_dec(v_unused_2032_);
v___x_1965_ = v_impl_1948_;
v_isShared_1966_ = v_isSharedCheck_2027_;
goto v_resetjp_1964_;
}
else
{
lean_dec(v_impl_1948_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_2027_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v_size_1967_; lean_object* v_k_1968_; lean_object* v_v_1969_; lean_object* v_l_1970_; lean_object* v_r_1971_; lean_object* v_size_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; uint8_t v___x_1975_; 
v_size_1967_ = lean_ctor_get(v_l_1954_, 0);
v_k_1968_ = lean_ctor_get(v_l_1954_, 1);
v_v_1969_ = lean_ctor_get(v_l_1954_, 2);
v_l_1970_ = lean_ctor_get(v_l_1954_, 3);
v_r_1971_ = lean_ctor_get(v_l_1954_, 4);
v_size_1972_ = lean_ctor_get(v_r_1955_, 0);
v___x_1973_ = lean_unsigned_to_nat(2u);
v___x_1974_ = lean_nat_mul(v___x_1973_, v_size_1972_);
v___x_1975_ = lean_nat_dec_lt(v_size_1967_, v___x_1974_);
lean_dec(v___x_1974_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_2003_; 
lean_inc(v_r_1971_);
lean_inc(v_l_1970_);
lean_inc(v_v_1969_);
lean_inc(v_k_1968_);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_l_1954_);
if (v_isSharedCheck_2003_ == 0)
{
lean_object* v_unused_2004_; lean_object* v_unused_2005_; lean_object* v_unused_2006_; lean_object* v_unused_2007_; lean_object* v_unused_2008_; 
v_unused_2004_ = lean_ctor_get(v_l_1954_, 4);
lean_dec(v_unused_2004_);
v_unused_2005_ = lean_ctor_get(v_l_1954_, 3);
lean_dec(v_unused_2005_);
v_unused_2006_ = lean_ctor_get(v_l_1954_, 2);
lean_dec(v_unused_2006_);
v_unused_2007_ = lean_ctor_get(v_l_1954_, 1);
lean_dec(v_unused_2007_);
v_unused_2008_ = lean_ctor_get(v_l_1954_, 0);
lean_dec(v_unused_2008_);
v___x_1977_ = v_l_1954_;
v_isShared_1978_ = v_isSharedCheck_2003_;
goto v_resetjp_1976_;
}
else
{
lean_dec(v_l_1954_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_2003_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1993_; 
v___x_1979_ = lean_nat_add(v___x_1949_, v_size_1950_);
v___x_1980_ = lean_nat_add(v___x_1979_, v_size_1951_);
lean_dec(v_size_1951_);
if (lean_obj_tag(v_l_1970_) == 0)
{
lean_object* v_size_2001_; 
v_size_2001_ = lean_ctor_get(v_l_1970_, 0);
lean_inc(v_size_2001_);
v___y_1993_ = v_size_2001_;
goto v___jp_1992_;
}
else
{
lean_object* v___x_2002_; 
v___x_2002_ = lean_unsigned_to_nat(0u);
v___y_1993_ = v___x_2002_;
goto v___jp_1992_;
}
v___jp_1981_:
{
lean_object* v___x_1985_; lean_object* v___x_1987_; 
v___x_1985_ = lean_nat_add(v___y_1982_, v___y_1984_);
lean_dec(v___y_1984_);
lean_dec(v___y_1982_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 4, v_r_1955_);
lean_ctor_set(v___x_1977_, 3, v_r_1971_);
lean_ctor_set(v___x_1977_, 2, v_v_1953_);
lean_ctor_set(v___x_1977_, 1, v_k_1952_);
lean_ctor_set(v___x_1977_, 0, v___x_1985_);
v___x_1987_ = v___x_1977_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1985_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v_k_1952_);
lean_ctor_set(v_reuseFailAlloc_1991_, 2, v_v_1953_);
lean_ctor_set(v_reuseFailAlloc_1991_, 3, v_r_1971_);
lean_ctor_set(v_reuseFailAlloc_1991_, 4, v_r_1955_);
v___x_1987_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
lean_object* v___x_1989_; 
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 4, v___x_1987_);
lean_ctor_set(v___x_1965_, 3, v___y_1983_);
lean_ctor_set(v___x_1965_, 2, v_v_1969_);
lean_ctor_set(v___x_1965_, 1, v_k_1968_);
lean_ctor_set(v___x_1965_, 0, v___x_1980_);
v___x_1989_ = v___x_1965_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1980_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v_k_1968_);
lean_ctor_set(v_reuseFailAlloc_1990_, 2, v_v_1969_);
lean_ctor_set(v_reuseFailAlloc_1990_, 3, v___y_1983_);
lean_ctor_set(v_reuseFailAlloc_1990_, 4, v___x_1987_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
v___jp_1992_:
{
lean_object* v___x_1994_; lean_object* v___x_1996_; 
v___x_1994_ = lean_nat_add(v___x_1979_, v___y_1993_);
lean_dec(v___y_1993_);
lean_dec(v___x_1979_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v_l_1970_);
lean_ctor_set(v___x_1944_, 0, v___x_1994_);
v___x_1996_ = v___x_1944_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1994_);
lean_ctor_set(v_reuseFailAlloc_2000_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_2000_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_2000_, 3, v_l_1941_);
lean_ctor_set(v_reuseFailAlloc_2000_, 4, v_l_1970_);
v___x_1996_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
lean_object* v___x_1997_; 
v___x_1997_ = lean_nat_add(v___x_1949_, v_size_1972_);
if (lean_obj_tag(v_r_1971_) == 0)
{
lean_object* v_size_1998_; 
v_size_1998_ = lean_ctor_get(v_r_1971_, 0);
lean_inc(v_size_1998_);
v___y_1982_ = v___x_1997_;
v___y_1983_ = v___x_1996_;
v___y_1984_ = v_size_1998_;
goto v___jp_1981_;
}
else
{
lean_object* v___x_1999_; 
v___x_1999_ = lean_unsigned_to_nat(0u);
v___y_1982_ = v___x_1997_;
v___y_1983_ = v___x_1996_;
v___y_1984_ = v___x_1999_;
goto v___jp_1981_;
}
}
}
}
}
else
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2013_; 
lean_del_object(v___x_1944_);
v___x_2009_ = lean_nat_add(v___x_1949_, v_size_1950_);
v___x_2010_ = lean_nat_add(v___x_2009_, v_size_1951_);
lean_dec(v_size_1951_);
v___x_2011_ = lean_nat_add(v___x_2009_, v_size_1967_);
lean_dec(v___x_2009_);
lean_inc_ref(v_l_1941_);
if (v_isShared_1966_ == 0)
{
lean_ctor_set(v___x_1965_, 4, v_l_1954_);
lean_ctor_set(v___x_1965_, 3, v_l_1941_);
lean_ctor_set(v___x_1965_, 2, v_v_1940_);
lean_ctor_set(v___x_1965_, 1, v_k_1939_);
lean_ctor_set(v___x_1965_, 0, v___x_2011_);
v___x_2013_ = v___x_1965_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2011_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_2026_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_2026_, 3, v_l_1941_);
lean_ctor_set(v_reuseFailAlloc_2026_, 4, v_l_1954_);
v___x_2013_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
v_isSharedCheck_2020_ = !lean_is_exclusive(v_l_1941_);
if (v_isSharedCheck_2020_ == 0)
{
lean_object* v_unused_2021_; lean_object* v_unused_2022_; lean_object* v_unused_2023_; lean_object* v_unused_2024_; lean_object* v_unused_2025_; 
v_unused_2021_ = lean_ctor_get(v_l_1941_, 4);
lean_dec(v_unused_2021_);
v_unused_2022_ = lean_ctor_get(v_l_1941_, 3);
lean_dec(v_unused_2022_);
v_unused_2023_ = lean_ctor_get(v_l_1941_, 2);
lean_dec(v_unused_2023_);
v_unused_2024_ = lean_ctor_get(v_l_1941_, 1);
lean_dec(v_unused_2024_);
v_unused_2025_ = lean_ctor_get(v_l_1941_, 0);
lean_dec(v_unused_2025_);
v___x_2015_ = v_l_1941_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_dec(v_l_1941_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 4, v_r_1955_);
lean_ctor_set(v___x_2015_, 3, v___x_2013_);
lean_ctor_set(v___x_2015_, 2, v_v_1953_);
lean_ctor_set(v___x_2015_, 1, v_k_1952_);
lean_ctor_set(v___x_2015_, 0, v___x_2010_);
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2010_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v_k_1952_);
lean_ctor_set(v_reuseFailAlloc_2019_, 2, v_v_1953_);
lean_ctor_set(v_reuseFailAlloc_2019_, 3, v___x_2013_);
lean_ctor_set(v_reuseFailAlloc_2019_, 4, v_r_1955_);
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
}
}
else
{
lean_object* v_l_2033_; 
v_l_2033_ = lean_ctor_get(v_impl_1948_, 3);
lean_inc(v_l_2033_);
if (lean_obj_tag(v_l_2033_) == 0)
{
lean_object* v_r_2034_; lean_object* v_k_2035_; lean_object* v_v_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2059_; 
v_r_2034_ = lean_ctor_get(v_impl_1948_, 4);
v_k_2035_ = lean_ctor_get(v_impl_1948_, 1);
v_v_2036_ = lean_ctor_get(v_impl_1948_, 2);
v_isSharedCheck_2059_ = !lean_is_exclusive(v_impl_1948_);
if (v_isSharedCheck_2059_ == 0)
{
lean_object* v_unused_2060_; lean_object* v_unused_2061_; 
v_unused_2060_ = lean_ctor_get(v_impl_1948_, 3);
lean_dec(v_unused_2060_);
v_unused_2061_ = lean_ctor_get(v_impl_1948_, 0);
lean_dec(v_unused_2061_);
v___x_2038_ = v_impl_1948_;
v_isShared_2039_ = v_isSharedCheck_2059_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_r_2034_);
lean_inc(v_v_2036_);
lean_inc(v_k_2035_);
lean_dec(v_impl_1948_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2059_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v_k_2040_; lean_object* v_v_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2055_; 
v_k_2040_ = lean_ctor_get(v_l_2033_, 1);
v_v_2041_ = lean_ctor_get(v_l_2033_, 2);
v_isSharedCheck_2055_ = !lean_is_exclusive(v_l_2033_);
if (v_isSharedCheck_2055_ == 0)
{
lean_object* v_unused_2056_; lean_object* v_unused_2057_; lean_object* v_unused_2058_; 
v_unused_2056_ = lean_ctor_get(v_l_2033_, 4);
lean_dec(v_unused_2056_);
v_unused_2057_ = lean_ctor_get(v_l_2033_, 3);
lean_dec(v_unused_2057_);
v_unused_2058_ = lean_ctor_get(v_l_2033_, 0);
lean_dec(v_unused_2058_);
v___x_2043_ = v_l_2033_;
v_isShared_2044_ = v_isSharedCheck_2055_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_v_2041_);
lean_inc(v_k_2040_);
lean_dec(v_l_2033_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2055_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2045_; lean_object* v___x_2047_; 
v___x_2045_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_2034_, 2);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 4, v_r_2034_);
lean_ctor_set(v___x_2043_, 3, v_r_2034_);
lean_ctor_set(v___x_2043_, 2, v_v_1940_);
lean_ctor_set(v___x_2043_, 1, v_k_1939_);
lean_ctor_set(v___x_2043_, 0, v___x_1949_);
v___x_2047_ = v___x_2043_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_1949_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_2054_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_2054_, 3, v_r_2034_);
lean_ctor_set(v_reuseFailAlloc_2054_, 4, v_r_2034_);
v___x_2047_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
lean_object* v___x_2049_; 
lean_inc(v_r_2034_);
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 3, v_r_2034_);
lean_ctor_set(v___x_2038_, 0, v___x_1949_);
v___x_2049_ = v___x_2038_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_1949_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v_k_2035_);
lean_ctor_set(v_reuseFailAlloc_2053_, 2, v_v_2036_);
lean_ctor_set(v_reuseFailAlloc_2053_, 3, v_r_2034_);
lean_ctor_set(v_reuseFailAlloc_2053_, 4, v_r_2034_);
v___x_2049_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
lean_object* v___x_2051_; 
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v___x_2049_);
lean_ctor_set(v___x_1944_, 3, v___x_2047_);
lean_ctor_set(v___x_1944_, 2, v_v_2041_);
lean_ctor_set(v___x_1944_, 1, v_k_2040_);
lean_ctor_set(v___x_1944_, 0, v___x_2045_);
v___x_2051_ = v___x_1944_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2045_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_k_2040_);
lean_ctor_set(v_reuseFailAlloc_2052_, 2, v_v_2041_);
lean_ctor_set(v_reuseFailAlloc_2052_, 3, v___x_2047_);
lean_ctor_set(v_reuseFailAlloc_2052_, 4, v___x_2049_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
}
}
else
{
lean_object* v_r_2062_; 
v_r_2062_ = lean_ctor_get(v_impl_1948_, 4);
lean_inc(v_r_2062_);
if (lean_obj_tag(v_r_2062_) == 0)
{
lean_object* v_k_2063_; lean_object* v_v_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2075_; 
v_k_2063_ = lean_ctor_get(v_impl_1948_, 1);
v_v_2064_ = lean_ctor_get(v_impl_1948_, 2);
v_isSharedCheck_2075_ = !lean_is_exclusive(v_impl_1948_);
if (v_isSharedCheck_2075_ == 0)
{
lean_object* v_unused_2076_; lean_object* v_unused_2077_; lean_object* v_unused_2078_; 
v_unused_2076_ = lean_ctor_get(v_impl_1948_, 4);
lean_dec(v_unused_2076_);
v_unused_2077_ = lean_ctor_get(v_impl_1948_, 3);
lean_dec(v_unused_2077_);
v_unused_2078_ = lean_ctor_get(v_impl_1948_, 0);
lean_dec(v_unused_2078_);
v___x_2066_ = v_impl_1948_;
v_isShared_2067_ = v_isSharedCheck_2075_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_v_2064_);
lean_inc(v_k_2063_);
lean_dec(v_impl_1948_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2075_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2068_; lean_object* v___x_2070_; 
v___x_2068_ = lean_unsigned_to_nat(3u);
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 4, v_l_2033_);
lean_ctor_set(v___x_2066_, 2, v_v_1940_);
lean_ctor_set(v___x_2066_, 1, v_k_1939_);
lean_ctor_set(v___x_2066_, 0, v___x_1949_);
v___x_2070_ = v___x_2066_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_1949_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_2074_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_2074_, 3, v_l_2033_);
lean_ctor_set(v_reuseFailAlloc_2074_, 4, v_l_2033_);
v___x_2070_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
lean_object* v___x_2072_; 
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v_r_2062_);
lean_ctor_set(v___x_1944_, 3, v___x_2070_);
lean_ctor_set(v___x_1944_, 2, v_v_2064_);
lean_ctor_set(v___x_1944_, 1, v_k_2063_);
lean_ctor_set(v___x_1944_, 0, v___x_2068_);
v___x_2072_ = v___x_1944_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2068_);
lean_ctor_set(v_reuseFailAlloc_2073_, 1, v_k_2063_);
lean_ctor_set(v_reuseFailAlloc_2073_, 2, v_v_2064_);
lean_ctor_set(v_reuseFailAlloc_2073_, 3, v___x_2070_);
lean_ctor_set(v_reuseFailAlloc_2073_, 4, v_r_2062_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
else
{
lean_object* v___x_2079_; lean_object* v___x_2081_; 
v___x_2079_ = lean_unsigned_to_nat(2u);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v_impl_1948_);
lean_ctor_set(v___x_1944_, 3, v_r_2062_);
lean_ctor_set(v___x_1944_, 0, v___x_2079_);
v___x_2081_ = v___x_1944_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2079_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_2082_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_2082_, 3, v_r_2062_);
lean_ctor_set(v_reuseFailAlloc_2082_, 4, v_impl_1948_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
}
}
else
{
lean_object* v___x_2084_; 
lean_dec(v_v_1940_);
lean_dec(v_k_1939_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 2, v_v_1936_);
lean_ctor_set(v___x_1944_, 1, v_k_1935_);
v___x_2084_ = v___x_1944_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_size_1938_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v_k_1935_);
lean_ctor_set(v_reuseFailAlloc_2085_, 2, v_v_1936_);
lean_ctor_set(v_reuseFailAlloc_2085_, 3, v_l_1941_);
lean_ctor_set(v_reuseFailAlloc_2085_, 4, v_r_1942_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
else
{
lean_object* v_impl_2086_; lean_object* v___x_2087_; 
lean_dec(v_size_1938_);
v_impl_2086_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_k_1935_, v_v_1936_, v_l_1941_);
v___x_2087_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1942_) == 0)
{
lean_object* v_size_2088_; lean_object* v_size_2089_; lean_object* v_k_2090_; lean_object* v_v_2091_; lean_object* v_l_2092_; lean_object* v_r_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; uint8_t v___x_2096_; 
v_size_2088_ = lean_ctor_get(v_r_1942_, 0);
v_size_2089_ = lean_ctor_get(v_impl_2086_, 0);
lean_inc(v_size_2089_);
v_k_2090_ = lean_ctor_get(v_impl_2086_, 1);
lean_inc(v_k_2090_);
v_v_2091_ = lean_ctor_get(v_impl_2086_, 2);
lean_inc(v_v_2091_);
v_l_2092_ = lean_ctor_get(v_impl_2086_, 3);
lean_inc(v_l_2092_);
v_r_2093_ = lean_ctor_get(v_impl_2086_, 4);
lean_inc(v_r_2093_);
v___x_2094_ = lean_unsigned_to_nat(3u);
v___x_2095_ = lean_nat_mul(v___x_2094_, v_size_2088_);
v___x_2096_ = lean_nat_dec_lt(v___x_2095_, v_size_2089_);
lean_dec(v___x_2095_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2100_; 
lean_dec(v_r_2093_);
lean_dec(v_l_2092_);
lean_dec(v_v_2091_);
lean_dec(v_k_2090_);
v___x_2097_ = lean_nat_add(v___x_2087_, v_size_2089_);
lean_dec(v_size_2089_);
v___x_2098_ = lean_nat_add(v___x_2097_, v_size_2088_);
lean_dec(v___x_2097_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 3, v_impl_2086_);
lean_ctor_set(v___x_1944_, 0, v___x_2098_);
v___x_2100_ = v___x_1944_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___x_2098_);
lean_ctor_set(v_reuseFailAlloc_2101_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_2101_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_2101_, 3, v_impl_2086_);
lean_ctor_set(v_reuseFailAlloc_2101_, 4, v_r_1942_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
else
{
lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2167_; 
v_isSharedCheck_2167_ = !lean_is_exclusive(v_impl_2086_);
if (v_isSharedCheck_2167_ == 0)
{
lean_object* v_unused_2168_; lean_object* v_unused_2169_; lean_object* v_unused_2170_; lean_object* v_unused_2171_; lean_object* v_unused_2172_; 
v_unused_2168_ = lean_ctor_get(v_impl_2086_, 4);
lean_dec(v_unused_2168_);
v_unused_2169_ = lean_ctor_get(v_impl_2086_, 3);
lean_dec(v_unused_2169_);
v_unused_2170_ = lean_ctor_get(v_impl_2086_, 2);
lean_dec(v_unused_2170_);
v_unused_2171_ = lean_ctor_get(v_impl_2086_, 1);
lean_dec(v_unused_2171_);
v_unused_2172_ = lean_ctor_get(v_impl_2086_, 0);
lean_dec(v_unused_2172_);
v___x_2103_ = v_impl_2086_;
v_isShared_2104_ = v_isSharedCheck_2167_;
goto v_resetjp_2102_;
}
else
{
lean_dec(v_impl_2086_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2167_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v_size_2105_; lean_object* v_size_2106_; lean_object* v_k_2107_; lean_object* v_v_2108_; lean_object* v_l_2109_; lean_object* v_r_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v_size_2105_ = lean_ctor_get(v_l_2092_, 0);
v_size_2106_ = lean_ctor_get(v_r_2093_, 0);
v_k_2107_ = lean_ctor_get(v_r_2093_, 1);
v_v_2108_ = lean_ctor_get(v_r_2093_, 2);
v_l_2109_ = lean_ctor_get(v_r_2093_, 3);
v_r_2110_ = lean_ctor_get(v_r_2093_, 4);
v___x_2111_ = lean_unsigned_to_nat(2u);
v___x_2112_ = lean_nat_mul(v___x_2111_, v_size_2105_);
v___x_2113_ = lean_nat_dec_lt(v_size_2106_, v___x_2112_);
lean_dec(v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2142_; 
lean_inc(v_r_2110_);
lean_inc(v_l_2109_);
lean_inc(v_v_2108_);
lean_inc(v_k_2107_);
v_isSharedCheck_2142_ = !lean_is_exclusive(v_r_2093_);
if (v_isSharedCheck_2142_ == 0)
{
lean_object* v_unused_2143_; lean_object* v_unused_2144_; lean_object* v_unused_2145_; lean_object* v_unused_2146_; lean_object* v_unused_2147_; 
v_unused_2143_ = lean_ctor_get(v_r_2093_, 4);
lean_dec(v_unused_2143_);
v_unused_2144_ = lean_ctor_get(v_r_2093_, 3);
lean_dec(v_unused_2144_);
v_unused_2145_ = lean_ctor_get(v_r_2093_, 2);
lean_dec(v_unused_2145_);
v_unused_2146_ = lean_ctor_get(v_r_2093_, 1);
lean_dec(v_unused_2146_);
v_unused_2147_ = lean_ctor_get(v_r_2093_, 0);
lean_dec(v_unused_2147_);
v___x_2115_ = v_r_2093_;
v_isShared_2116_ = v_isSharedCheck_2142_;
goto v_resetjp_2114_;
}
else
{
lean_dec(v_r_2093_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2142_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2122_; lean_object* v___x_2130_; lean_object* v___y_2132_; 
v___x_2117_ = lean_nat_add(v___x_2087_, v_size_2089_);
lean_dec(v_size_2089_);
v___x_2118_ = lean_nat_add(v___x_2117_, v_size_2088_);
lean_dec(v___x_2117_);
v___x_2130_ = lean_nat_add(v___x_2087_, v_size_2105_);
if (lean_obj_tag(v_l_2109_) == 0)
{
lean_object* v_size_2140_; 
v_size_2140_ = lean_ctor_get(v_l_2109_, 0);
lean_inc(v_size_2140_);
v___y_2132_ = v_size_2140_;
goto v___jp_2131_;
}
else
{
lean_object* v___x_2141_; 
v___x_2141_ = lean_unsigned_to_nat(0u);
v___y_2132_ = v___x_2141_;
goto v___jp_2131_;
}
v___jp_2119_:
{
lean_object* v___x_2123_; lean_object* v___x_2125_; 
v___x_2123_ = lean_nat_add(v___y_2121_, v___y_2122_);
lean_dec(v___y_2122_);
lean_dec(v___y_2121_);
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 4, v_r_1942_);
lean_ctor_set(v___x_2115_, 3, v_r_2110_);
lean_ctor_set(v___x_2115_, 2, v_v_1940_);
lean_ctor_set(v___x_2115_, 1, v_k_1939_);
lean_ctor_set(v___x_2115_, 0, v___x_2123_);
v___x_2125_ = v___x_2115_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2123_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_2129_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_2129_, 3, v_r_2110_);
lean_ctor_set(v_reuseFailAlloc_2129_, 4, v_r_1942_);
v___x_2125_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
lean_object* v___x_2127_; 
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 4, v___x_2125_);
lean_ctor_set(v___x_2103_, 3, v___y_2120_);
lean_ctor_set(v___x_2103_, 2, v_v_2108_);
lean_ctor_set(v___x_2103_, 1, v_k_2107_);
lean_ctor_set(v___x_2103_, 0, v___x_2118_);
v___x_2127_ = v___x_2103_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2118_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v_k_2107_);
lean_ctor_set(v_reuseFailAlloc_2128_, 2, v_v_2108_);
lean_ctor_set(v_reuseFailAlloc_2128_, 3, v___y_2120_);
lean_ctor_set(v_reuseFailAlloc_2128_, 4, v___x_2125_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
v___jp_2131_:
{
lean_object* v___x_2133_; lean_object* v___x_2135_; 
v___x_2133_ = lean_nat_add(v___x_2130_, v___y_2132_);
lean_dec(v___y_2132_);
lean_dec(v___x_2130_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v_l_2109_);
lean_ctor_set(v___x_1944_, 3, v_l_2092_);
lean_ctor_set(v___x_1944_, 2, v_v_2091_);
lean_ctor_set(v___x_1944_, 1, v_k_2090_);
lean_ctor_set(v___x_1944_, 0, v___x_2133_);
v___x_2135_ = v___x_1944_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2133_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v_k_2090_);
lean_ctor_set(v_reuseFailAlloc_2139_, 2, v_v_2091_);
lean_ctor_set(v_reuseFailAlloc_2139_, 3, v_l_2092_);
lean_ctor_set(v_reuseFailAlloc_2139_, 4, v_l_2109_);
v___x_2135_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
lean_object* v___x_2136_; 
v___x_2136_ = lean_nat_add(v___x_2087_, v_size_2088_);
if (lean_obj_tag(v_r_2110_) == 0)
{
lean_object* v_size_2137_; 
v_size_2137_ = lean_ctor_get(v_r_2110_, 0);
lean_inc(v_size_2137_);
v___y_2120_ = v___x_2135_;
v___y_2121_ = v___x_2136_;
v___y_2122_ = v_size_2137_;
goto v___jp_2119_;
}
else
{
lean_object* v___x_2138_; 
v___x_2138_ = lean_unsigned_to_nat(0u);
v___y_2120_ = v___x_2135_;
v___y_2121_ = v___x_2136_;
v___y_2122_ = v___x_2138_;
goto v___jp_2119_;
}
}
}
}
}
else
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2153_; 
lean_del_object(v___x_1944_);
v___x_2148_ = lean_nat_add(v___x_2087_, v_size_2089_);
lean_dec(v_size_2089_);
v___x_2149_ = lean_nat_add(v___x_2148_, v_size_2088_);
lean_dec(v___x_2148_);
v___x_2150_ = lean_nat_add(v___x_2087_, v_size_2088_);
v___x_2151_ = lean_nat_add(v___x_2150_, v_size_2106_);
lean_dec(v___x_2150_);
lean_inc_ref(v_r_1942_);
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 4, v_r_1942_);
lean_ctor_set(v___x_2103_, 3, v_r_2093_);
lean_ctor_set(v___x_2103_, 2, v_v_1940_);
lean_ctor_set(v___x_2103_, 1, v_k_1939_);
lean_ctor_set(v___x_2103_, 0, v___x_2151_);
v___x_2153_ = v___x_2103_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2151_);
lean_ctor_set(v_reuseFailAlloc_2166_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_2166_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_2166_, 3, v_r_2093_);
lean_ctor_set(v_reuseFailAlloc_2166_, 4, v_r_1942_);
v___x_2153_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
v_isSharedCheck_2160_ = !lean_is_exclusive(v_r_1942_);
if (v_isSharedCheck_2160_ == 0)
{
lean_object* v_unused_2161_; lean_object* v_unused_2162_; lean_object* v_unused_2163_; lean_object* v_unused_2164_; lean_object* v_unused_2165_; 
v_unused_2161_ = lean_ctor_get(v_r_1942_, 4);
lean_dec(v_unused_2161_);
v_unused_2162_ = lean_ctor_get(v_r_1942_, 3);
lean_dec(v_unused_2162_);
v_unused_2163_ = lean_ctor_get(v_r_1942_, 2);
lean_dec(v_unused_2163_);
v_unused_2164_ = lean_ctor_get(v_r_1942_, 1);
lean_dec(v_unused_2164_);
v_unused_2165_ = lean_ctor_get(v_r_1942_, 0);
lean_dec(v_unused_2165_);
v___x_2155_ = v_r_1942_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_dec(v_r_1942_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
lean_ctor_set(v___x_2155_, 4, v___x_2153_);
lean_ctor_set(v___x_2155_, 3, v_l_2092_);
lean_ctor_set(v___x_2155_, 2, v_v_2091_);
lean_ctor_set(v___x_2155_, 1, v_k_2090_);
lean_ctor_set(v___x_2155_, 0, v___x_2149_);
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2149_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_k_2090_);
lean_ctor_set(v_reuseFailAlloc_2159_, 2, v_v_2091_);
lean_ctor_set(v_reuseFailAlloc_2159_, 3, v_l_2092_);
lean_ctor_set(v_reuseFailAlloc_2159_, 4, v___x_2153_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_2173_; 
v_l_2173_ = lean_ctor_get(v_impl_2086_, 3);
lean_inc(v_l_2173_);
if (lean_obj_tag(v_l_2173_) == 0)
{
lean_object* v_r_2174_; lean_object* v_k_2175_; lean_object* v_v_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2187_; 
v_r_2174_ = lean_ctor_get(v_impl_2086_, 4);
v_k_2175_ = lean_ctor_get(v_impl_2086_, 1);
v_v_2176_ = lean_ctor_get(v_impl_2086_, 2);
v_isSharedCheck_2187_ = !lean_is_exclusive(v_impl_2086_);
if (v_isSharedCheck_2187_ == 0)
{
lean_object* v_unused_2188_; lean_object* v_unused_2189_; 
v_unused_2188_ = lean_ctor_get(v_impl_2086_, 3);
lean_dec(v_unused_2188_);
v_unused_2189_ = lean_ctor_get(v_impl_2086_, 0);
lean_dec(v_unused_2189_);
v___x_2178_ = v_impl_2086_;
v_isShared_2179_ = v_isSharedCheck_2187_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_r_2174_);
lean_inc(v_v_2176_);
lean_inc(v_k_2175_);
lean_dec(v_impl_2086_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2187_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2180_; lean_object* v___x_2182_; 
v___x_2180_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_2174_);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 3, v_r_2174_);
lean_ctor_set(v___x_2178_, 2, v_v_1940_);
lean_ctor_set(v___x_2178_, 1, v_k_1939_);
lean_ctor_set(v___x_2178_, 0, v___x_2087_);
v___x_2182_ = v___x_2178_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2087_);
lean_ctor_set(v_reuseFailAlloc_2186_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_2186_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_2186_, 3, v_r_2174_);
lean_ctor_set(v_reuseFailAlloc_2186_, 4, v_r_2174_);
v___x_2182_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
lean_object* v___x_2184_; 
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v___x_2182_);
lean_ctor_set(v___x_1944_, 3, v_l_2173_);
lean_ctor_set(v___x_1944_, 2, v_v_2176_);
lean_ctor_set(v___x_1944_, 1, v_k_2175_);
lean_ctor_set(v___x_1944_, 0, v___x_2180_);
v___x_2184_ = v___x_1944_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2180_);
lean_ctor_set(v_reuseFailAlloc_2185_, 1, v_k_2175_);
lean_ctor_set(v_reuseFailAlloc_2185_, 2, v_v_2176_);
lean_ctor_set(v_reuseFailAlloc_2185_, 3, v_l_2173_);
lean_ctor_set(v_reuseFailAlloc_2185_, 4, v___x_2182_);
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
else
{
lean_object* v_r_2190_; 
v_r_2190_ = lean_ctor_get(v_impl_2086_, 4);
lean_inc(v_r_2190_);
if (lean_obj_tag(v_r_2190_) == 0)
{
lean_object* v_k_2191_; lean_object* v_v_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2215_; 
v_k_2191_ = lean_ctor_get(v_impl_2086_, 1);
v_v_2192_ = lean_ctor_get(v_impl_2086_, 2);
v_isSharedCheck_2215_ = !lean_is_exclusive(v_impl_2086_);
if (v_isSharedCheck_2215_ == 0)
{
lean_object* v_unused_2216_; lean_object* v_unused_2217_; lean_object* v_unused_2218_; 
v_unused_2216_ = lean_ctor_get(v_impl_2086_, 4);
lean_dec(v_unused_2216_);
v_unused_2217_ = lean_ctor_get(v_impl_2086_, 3);
lean_dec(v_unused_2217_);
v_unused_2218_ = lean_ctor_get(v_impl_2086_, 0);
lean_dec(v_unused_2218_);
v___x_2194_ = v_impl_2086_;
v_isShared_2195_ = v_isSharedCheck_2215_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_v_2192_);
lean_inc(v_k_2191_);
lean_dec(v_impl_2086_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2215_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v_k_2196_; lean_object* v_v_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2211_; 
v_k_2196_ = lean_ctor_get(v_r_2190_, 1);
v_v_2197_ = lean_ctor_get(v_r_2190_, 2);
v_isSharedCheck_2211_ = !lean_is_exclusive(v_r_2190_);
if (v_isSharedCheck_2211_ == 0)
{
lean_object* v_unused_2212_; lean_object* v_unused_2213_; lean_object* v_unused_2214_; 
v_unused_2212_ = lean_ctor_get(v_r_2190_, 4);
lean_dec(v_unused_2212_);
v_unused_2213_ = lean_ctor_get(v_r_2190_, 3);
lean_dec(v_unused_2213_);
v_unused_2214_ = lean_ctor_get(v_r_2190_, 0);
lean_dec(v_unused_2214_);
v___x_2199_ = v_r_2190_;
v_isShared_2200_ = v_isSharedCheck_2211_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_v_2197_);
lean_inc(v_k_2196_);
lean_dec(v_r_2190_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2211_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2201_; lean_object* v___x_2203_; 
v___x_2201_ = lean_unsigned_to_nat(3u);
if (v_isShared_2200_ == 0)
{
lean_ctor_set(v___x_2199_, 4, v_l_2173_);
lean_ctor_set(v___x_2199_, 3, v_l_2173_);
lean_ctor_set(v___x_2199_, 2, v_v_2192_);
lean_ctor_set(v___x_2199_, 1, v_k_2191_);
lean_ctor_set(v___x_2199_, 0, v___x_2087_);
v___x_2203_ = v___x_2199_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2087_);
lean_ctor_set(v_reuseFailAlloc_2210_, 1, v_k_2191_);
lean_ctor_set(v_reuseFailAlloc_2210_, 2, v_v_2192_);
lean_ctor_set(v_reuseFailAlloc_2210_, 3, v_l_2173_);
lean_ctor_set(v_reuseFailAlloc_2210_, 4, v_l_2173_);
v___x_2203_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
lean_object* v___x_2205_; 
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 4, v_l_2173_);
lean_ctor_set(v___x_2194_, 2, v_v_1940_);
lean_ctor_set(v___x_2194_, 1, v_k_1939_);
lean_ctor_set(v___x_2194_, 0, v___x_2087_);
v___x_2205_ = v___x_2194_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2087_);
lean_ctor_set(v_reuseFailAlloc_2209_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_2209_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_2209_, 3, v_l_2173_);
lean_ctor_set(v_reuseFailAlloc_2209_, 4, v_l_2173_);
v___x_2205_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
lean_object* v___x_2207_; 
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v___x_2205_);
lean_ctor_set(v___x_1944_, 3, v___x_2203_);
lean_ctor_set(v___x_1944_, 2, v_v_2197_);
lean_ctor_set(v___x_1944_, 1, v_k_2196_);
lean_ctor_set(v___x_1944_, 0, v___x_2201_);
v___x_2207_ = v___x_1944_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2201_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v_k_2196_);
lean_ctor_set(v_reuseFailAlloc_2208_, 2, v_v_2197_);
lean_ctor_set(v_reuseFailAlloc_2208_, 3, v___x_2203_);
lean_ctor_set(v_reuseFailAlloc_2208_, 4, v___x_2205_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
}
}
else
{
lean_object* v___x_2219_; lean_object* v___x_2221_; 
v___x_2219_ = lean_unsigned_to_nat(2u);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 4, v_r_2190_);
lean_ctor_set(v___x_1944_, 3, v_impl_2086_);
lean_ctor_set(v___x_1944_, 0, v___x_2219_);
v___x_2221_ = v___x_1944_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2219_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_k_1939_);
lean_ctor_set(v_reuseFailAlloc_2222_, 2, v_v_1940_);
lean_ctor_set(v_reuseFailAlloc_2222_, 3, v_impl_2086_);
lean_ctor_set(v_reuseFailAlloc_2222_, 4, v_r_2190_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2224_ = lean_unsigned_to_nat(1u);
v___x_2225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2224_);
lean_ctor_set(v___x_2225_, 1, v_k_1935_);
lean_ctor_set(v___x_2225_, 2, v_v_1936_);
lean_ctor_set(v___x_2225_, 3, v_t_1937_);
lean_ctor_set(v___x_2225_, 4, v_t_1937_);
return v___x_2225_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(lean_object* v_as_x27_2226_, lean_object* v_b_2227_){
_start:
{
if (lean_obj_tag(v_as_x27_2226_) == 0)
{
return v_b_2227_;
}
else
{
lean_object* v_head_2228_; lean_object* v_tail_2229_; lean_object* v_fst_2230_; lean_object* v_snd_2231_; lean_object* v_r_2232_; 
v_head_2228_ = lean_ctor_get(v_as_x27_2226_, 0);
v_tail_2229_ = lean_ctor_get(v_as_x27_2226_, 1);
v_fst_2230_ = lean_ctor_get(v_head_2228_, 0);
v_snd_2231_ = lean_ctor_get(v_head_2228_, 1);
lean_inc(v_snd_2231_);
lean_inc(v_fst_2230_);
v_r_2232_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_fst_2230_, v_snd_2231_, v_b_2227_);
v_as_x27_2226_ = v_tail_2229_;
v_b_2227_ = v_r_2232_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg___boxed(lean_object* v_as_x27_2234_, lean_object* v_b_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_as_x27_2234_, v_b_2235_);
lean_dec(v_as_x27_2234_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(lean_object* v_firsts_2237_, lean_object* v_n_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2275_; lean_object* v_val_2276_; lean_object* v___x_2278_; lean_object* v___y_2280_; lean_object* v_env_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2278_ = lean_st_ref_get(v___y_2240_);
v_env_2295_ = lean_ctor_get(v___x_2278_, 0);
lean_inc_ref(v_env_2295_);
lean_dec(v___x_2278_);
v___x_2296_ = l_Lean_Environment_constants(v_env_2295_);
v___x_2297_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___redArg(v___x_2296_, v_n_2238_);
lean_dec_ref(v___x_2296_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v___x_2298_; 
v___x_2298_ = lean_box(0);
v___y_2280_ = v___x_2298_;
goto v___jp_2279_;
}
else
{
lean_object* v_val_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v_val_2299_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_val_2299_);
lean_dec_ref(v___x_2297_);
v___x_2300_ = l_Lean_ConstantInfo_levelParams(v_val_2299_);
lean_dec(v_val_2299_);
v___x_2301_ = lean_box(0);
v___x_2302_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__14(v___x_2300_, v___x_2301_);
v___y_2280_ = v___x_2302_;
goto v___jp_2279_;
}
v___jp_2242_:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; uint8_t v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; uint8_t v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v_r_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2245_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__0));
v___x_2246_ = lean_unsigned_to_nat(0u);
v___x_2247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2246_);
lean_ctor_set(v___x_2247_, 1, v___y_2244_);
v___x_2248_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2248_, 0, v___x_2245_);
lean_ctor_set(v___x_2248_, 1, v___x_2247_);
v___x_2249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
lean_ctor_set(v___x_2249_, 1, v___x_2245_);
v___x_2250_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___redArg___lam__2___closed__2));
v___x_2251_ = lean_box(2);
v___x_2252_ = 1;
lean_inc_n(v_n_2238_, 3);
v___x_2253_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_2238_, v___x_2252_);
v___x_2254_ = lean_string_utf8_byte_size(v___x_2253_);
v___x_2255_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2253_);
lean_ctor_set(v___x_2255_, 1, v___x_2246_);
lean_ctor_set(v___x_2255_, 2, v___x_2254_);
v___x_2256_ = lean_box(0);
v___x_2257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2257_, 0, v_n_2238_);
lean_ctor_set(v___x_2257_, 1, v___x_2256_);
v___x_2258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
lean_ctor_set(v___x_2258_, 1, v___x_2256_);
v___x_2259_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2251_);
lean_ctor_set(v___x_2259_, 1, v___x_2255_);
lean_ctor_set(v___x_2259_, 2, v_n_2238_);
lean_ctor_set(v___x_2259_, 3, v___x_2258_);
v___x_2260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2250_);
lean_ctor_set(v___x_2260_, 1, v___x_2259_);
v___x_2261_ = l_Lean_LocalContext_empty;
v___x_2262_ = lean_box(0);
v___x_2263_ = l_Lean_Expr_const___override(v_n_2238_, v___y_2243_);
v___x_2264_ = 0;
v___x_2265_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2265_, 0, v___x_2260_);
lean_ctor_set(v___x_2265_, 1, v___x_2261_);
lean_ctor_set(v___x_2265_, 2, v___x_2262_);
lean_ctor_set(v___x_2265_, 3, v___x_2263_);
lean_ctor_set_uint8(v___x_2265_, sizeof(void*)*4, v___x_2264_);
lean_ctor_set_uint8(v___x_2265_, sizeof(void*)*4 + 1, v___x_2264_);
v___x_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2265_);
v___x_2267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2246_);
lean_ctor_set(v___x_2267_, 1, v___x_2266_);
v___x_2268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
lean_ctor_set(v___x_2268_, 1, v___x_2256_);
v_r_2269_ = lean_box(1);
v___x_2270_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v___x_2268_, v_r_2269_);
lean_dec_ref(v___x_2268_);
v___x_2271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2249_);
lean_ctor_set(v___x_2271_, 1, v___x_2270_);
v___x_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2271_);
v___x_2273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
return v___x_2273_;
}
v___jp_2274_:
{
lean_object* v___x_2277_; 
v___x_2277_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2277_, 0, v_val_2276_);
v___y_2243_ = v___y_2275_;
v___y_2244_ = v___x_2277_;
goto v___jp_2242_;
}
v___jp_2279_:
{
lean_object* v___x_2281_; lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2294_; 
lean_inc(v_n_2238_);
v___x_2281_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_n_2238_, v___y_2240_);
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2284_ = v___x_2281_;
v_isShared_2285_ = v_isSharedCheck_2294_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2281_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2294_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
if (lean_obj_tag(v_a_2282_) == 0)
{
lean_object* v___x_2286_; 
v___x_2286_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg(v_firsts_2237_, v_n_2238_);
if (lean_obj_tag(v___x_2286_) == 0)
{
uint8_t v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2290_; 
v___x_2287_ = 1;
lean_inc(v_n_2238_);
v___x_2288_ = l_Lean_Name_toString(v_n_2238_, v___x_2287_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set_tag(v___x_2284_, 3);
lean_ctor_set(v___x_2284_, 0, v___x_2288_);
v___x_2290_ = v___x_2284_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2288_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
v___y_2243_ = v___y_2280_;
v___y_2244_ = v___x_2290_;
goto v___jp_2242_;
}
}
else
{
lean_object* v_val_2292_; 
lean_del_object(v___x_2284_);
v_val_2292_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_val_2292_);
lean_dec_ref(v___x_2286_);
v___y_2275_ = v___y_2280_;
v_val_2276_ = v_val_2292_;
goto v___jp_2274_;
}
}
else
{
lean_object* v_val_2293_; 
lean_del_object(v___x_2284_);
v_val_2293_ = lean_ctor_get(v_a_2282_, 0);
lean_inc(v_val_2293_);
lean_dec_ref(v_a_2282_);
v___y_2275_ = v___y_2280_;
v_val_2276_ = v_val_2293_;
goto v___jp_2274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6___boxed(lean_object* v_firsts_2303_, lean_object* v_n_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_firsts_2303_, v_n_2304_, v___y_2305_, v___y_2306_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec(v_firsts_2303_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(lean_object* v_a_2309_, lean_object* v_x_2310_, lean_object* v_x_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
if (lean_obj_tag(v_x_2310_) == 0)
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = l_List_reverse___redArg(v_x_2311_);
v___x_2316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
return v___x_2316_;
}
else
{
lean_object* v_head_2317_; lean_object* v_tail_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2336_; 
v_head_2317_ = lean_ctor_get(v_x_2310_, 0);
v_tail_2318_ = lean_ctor_get(v_x_2310_, 1);
v_isSharedCheck_2336_ = !lean_is_exclusive(v_x_2310_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2320_ = v_x_2310_;
v_isShared_2321_ = v_isSharedCheck_2336_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_tail_2318_);
lean_inc(v_head_2317_);
lean_dec(v_x_2310_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2336_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2322_; 
v___x_2322_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6(v_a_2309_, v_head_2317_, v___y_2312_, v___y_2313_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v_a_2323_; lean_object* v___x_2325_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_a_2323_);
lean_dec_ref(v___x_2322_);
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 1, v_x_2311_);
lean_ctor_set(v___x_2320_, 0, v_a_2323_);
v___x_2325_ = v___x_2320_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2323_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_x_2311_);
v___x_2325_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
v_x_2310_ = v_tail_2318_;
v_x_2311_ = v___x_2325_;
goto _start;
}
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
lean_del_object(v___x_2320_);
lean_dec(v_tail_2318_);
lean_dec(v_x_2311_);
v_a_2328_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2322_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2322_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7___boxed(lean_object* v_a_2337_, lean_object* v_x_2338_, lean_object* v_x_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_2337_, v_x_2338_, v_x_2339_, v___y_2340_, v___y_2341_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
lean_dec(v_a_2337_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(lean_object* v_val_2344_, lean_object* v___x_2345_, lean_object* v___x_2346_, lean_object* v_a_2347_, lean_object* v_b_2348_){
_start:
{
lean_object* v_it_2350_; lean_object* v_startInclusive_2351_; lean_object* v_endExclusive_2352_; 
if (lean_obj_tag(v_a_2347_) == 0)
{
lean_object* v_currPos_2357_; lean_object* v_searcher_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2384_; 
v_currPos_2357_ = lean_ctor_get(v_a_2347_, 0);
v_searcher_2358_ = lean_ctor_get(v_a_2347_, 1);
v_isSharedCheck_2384_ = !lean_is_exclusive(v_a_2347_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2360_ = v_a_2347_;
v_isShared_2361_ = v_isSharedCheck_2384_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_searcher_2358_);
lean_inc(v_currPos_2357_);
lean_dec(v_a_2347_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2384_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v_startInclusive_2362_; lean_object* v_endExclusive_2363_; lean_object* v___x_2364_; uint8_t v___x_2365_; 
v_startInclusive_2362_ = lean_ctor_get(v___x_2345_, 1);
v_endExclusive_2363_ = lean_ctor_get(v___x_2345_, 2);
v___x_2364_ = lean_nat_sub(v_endExclusive_2363_, v_startInclusive_2362_);
v___x_2365_ = lean_nat_dec_eq(v_searcher_2358_, v___x_2364_);
lean_dec(v___x_2364_);
if (v___x_2365_ == 0)
{
uint32_t v___x_2366_; uint32_t v___x_2367_; uint8_t v___x_2368_; 
v___x_2366_ = 10;
v___x_2367_ = lean_string_utf8_get_fast(v_val_2344_, v_searcher_2358_);
v___x_2368_ = lean_uint32_dec_eq(v___x_2367_, v___x_2366_);
if (v___x_2368_ == 0)
{
lean_object* v___x_2369_; lean_object* v___x_2371_; 
v___x_2369_ = lean_string_utf8_next_fast(v_val_2344_, v_searcher_2358_);
lean_dec(v_searcher_2358_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 1, v___x_2369_);
v___x_2371_ = v___x_2360_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_currPos_2357_);
lean_ctor_set(v_reuseFailAlloc_2373_, 1, v___x_2369_);
v___x_2371_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
v_a_2347_ = v___x_2371_;
goto _start;
}
}
else
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v_slice_2377_; lean_object* v_nextIt_2379_; 
v___x_2374_ = lean_string_utf8_next_fast(v_val_2344_, v_searcher_2358_);
v___x_2375_ = lean_nat_sub(v___x_2374_, v_searcher_2358_);
v___x_2376_ = lean_nat_add(v_searcher_2358_, v___x_2375_);
lean_dec(v___x_2375_);
v_slice_2377_ = l_String_Slice_subslice_x21(v___x_2345_, v_currPos_2357_, v_searcher_2358_);
lean_inc(v___x_2376_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 1, v___x_2376_);
lean_ctor_set(v___x_2360_, 0, v___x_2376_);
v_nextIt_2379_ = v___x_2360_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v___x_2376_);
lean_ctor_set(v_reuseFailAlloc_2382_, 1, v___x_2376_);
v_nextIt_2379_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
lean_object* v_startInclusive_2380_; lean_object* v_endExclusive_2381_; 
v_startInclusive_2380_ = lean_ctor_get(v_slice_2377_, 0);
lean_inc(v_startInclusive_2380_);
v_endExclusive_2381_ = lean_ctor_get(v_slice_2377_, 1);
lean_inc(v_endExclusive_2381_);
lean_dec_ref(v_slice_2377_);
v_it_2350_ = v_nextIt_2379_;
v_startInclusive_2351_ = v_startInclusive_2380_;
v_endExclusive_2352_ = v_endExclusive_2381_;
goto v___jp_2349_;
}
}
}
else
{
lean_object* v___x_2383_; 
lean_del_object(v___x_2360_);
lean_dec(v_searcher_2358_);
v___x_2383_ = lean_box(1);
lean_inc(v___x_2346_);
v_it_2350_ = v___x_2383_;
v_startInclusive_2351_ = v_currPos_2357_;
v_endExclusive_2352_ = v___x_2346_;
goto v___jp_2349_;
}
}
}
else
{
lean_dec(v___x_2346_);
return v_b_2348_;
}
v___jp_2349_:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2353_ = lean_string_utf8_extract(v_val_2344_, v_startInclusive_2351_, v_endExclusive_2352_);
lean_dec(v_endExclusive_2352_);
lean_dec(v_startInclusive_2351_);
v___x_2354_ = l_Lean_stringToMessageData(v___x_2353_);
v___x_2355_ = lean_array_push(v_b_2348_, v___x_2354_);
v_a_2347_ = v_it_2350_;
v_b_2348_ = v___x_2355_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg___boxed(lean_object* v_val_2385_, lean_object* v___x_2386_, lean_object* v___x_2387_, lean_object* v_a_2388_, lean_object* v_b_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2385_, v___x_2386_, v___x_2387_, v_a_2388_, v_b_2389_);
lean_dec_ref(v___x_2386_);
lean_dec_ref(v_val_2385_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__17(lean_object* v_init_2391_, lean_object* v_x_2392_){
_start:
{
if (lean_obj_tag(v_x_2392_) == 0)
{
lean_object* v_k_2393_; lean_object* v_l_2394_; lean_object* v_r_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v_k_2393_ = lean_ctor_get(v_x_2392_, 1);
lean_inc(v_k_2393_);
v_l_2394_ = lean_ctor_get(v_x_2392_, 3);
lean_inc(v_l_2394_);
v_r_2395_ = lean_ctor_get(v_x_2392_, 4);
lean_inc(v_r_2395_);
lean_dec_ref(v_x_2392_);
v___x_2396_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__17(v_init_2391_, v_l_2394_);
v___x_2397_ = lean_array_push(v___x_2396_, v_k_2393_);
v_init_2391_ = v___x_2397_;
v_x_2392_ = v_r_2395_;
goto _start;
}
else
{
return v_init_2391_;
}
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2(void){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2402_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__1));
v___x_2403_ = l_Lean_stringToMessageData(v___x_2402_);
return v___x_2403_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4(void){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2405_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__3));
v___x_2406_ = l_Lean_stringToMessageData(v___x_2405_);
return v___x_2406_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6(void){
_start:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2408_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__5));
v___x_2409_ = l_Lean_stringToMessageData(v___x_2408_);
return v___x_2409_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9(void){
_start:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2413_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__8));
v___x_2414_ = l_Lean_MessageData_ofFormat(v___x_2413_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_x_2417_, lean_object* v_x_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
if (lean_obj_tag(v_x_2417_) == 0)
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2422_ = l_List_reverse___redArg(v_x_2418_);
v___x_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2422_);
return v___x_2423_;
}
else
{
lean_object* v_head_2424_; lean_object* v_tail_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2522_; 
v_head_2424_ = lean_ctor_get(v_x_2417_, 0);
v_tail_2425_ = lean_ctor_get(v_x_2417_, 1);
v_isSharedCheck_2522_ = !lean_is_exclusive(v_x_2417_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2427_ = v_x_2417_;
v_isShared_2428_ = v_isSharedCheck_2522_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_tail_2425_);
lean_inc(v_head_2424_);
lean_dec(v_x_2417_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2522_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___y_2430_; lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2433_; lean_object* v_snd_2442_; lean_object* v_fst_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2521_; 
v_snd_2442_ = lean_ctor_get(v_head_2424_, 1);
v_fst_2443_ = lean_ctor_get(v_head_2424_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v_head_2424_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2445_ = v_head_2424_;
v_isShared_2446_ = v_isSharedCheck_2521_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_snd_2442_);
lean_inc(v_fst_2443_);
lean_dec(v_head_2424_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2521_;
goto v_resetjp_2444_;
}
v___jp_2429_:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2439_; 
v___x_2434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___y_2431_);
lean_ctor_set(v___x_2434_, 1, v___y_2433_);
v___x_2435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2434_);
lean_ctor_set(v___x_2435_, 1, v___y_2432_);
v___x_2436_ = l_Lean_MessageData_nestD(v___x_2435_);
lean_inc_ref(v___y_2430_);
v___x_2437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___y_2430_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 1, v_x_2418_);
lean_ctor_set(v___x_2427_, 0, v___x_2437_);
v___x_2439_ = v___x_2427_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2437_);
lean_ctor_set(v_reuseFailAlloc_2441_, 1, v_x_2418_);
v___x_2439_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
v_x_2417_ = v_tail_2425_;
v_x_2418_ = v___x_2439_;
goto _start;
}
}
v_resetjp_2444_:
{
lean_object* v_fst_2447_; lean_object* v_snd_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2520_; 
v_fst_2447_ = lean_ctor_get(v_snd_2442_, 0);
v_snd_2448_ = lean_ctor_get(v_snd_2442_, 1);
v_isSharedCheck_2520_ = !lean_is_exclusive(v_snd_2442_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2450_ = v_snd_2442_;
v_isShared_2451_ = v_isSharedCheck_2520_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_snd_2448_);
lean_inc(v_fst_2447_);
lean_dec(v_snd_2442_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2520_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v_a_2475_; lean_object* v___y_2491_; lean_object* v___x_2500_; 
v___x_2500_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_a_2416_, v_fst_2443_);
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_object* v___x_2501_; 
v___x_2501_ = l_Lean_MessageData_nil;
v_a_2475_ = v___x_2501_;
goto v___jp_2474_;
}
else
{
lean_object* v_val_2502_; 
v_val_2502_ = lean_ctor_get(v___x_2500_, 0);
lean_inc(v_val_2502_);
lean_dec_ref(v___x_2500_);
if (lean_obj_tag(v_val_2502_) == 0)
{
lean_object* v_size_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___x_2511_; uint8_t v___x_2512_; 
v_size_2503_ = lean_ctor_get(v_val_2502_, 0);
v___x_2504_ = lean_mk_empty_array_with_capacity(v_size_2503_);
v___x_2505_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__17(v___x_2504_, v_val_2502_);
v___x_2506_ = lean_array_get_size(v___x_2505_);
v___x_2511_ = lean_unsigned_to_nat(0u);
v___x_2512_ = lean_nat_dec_eq(v___x_2506_, v___x_2511_);
if (v___x_2512_ == 0)
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___y_2516_; uint8_t v___x_2518_; 
v___x_2513_ = lean_unsigned_to_nat(1u);
v___x_2514_ = lean_nat_sub(v___x_2506_, v___x_2513_);
v___x_2518_ = lean_nat_dec_le(v___x_2511_, v___x_2514_);
if (v___x_2518_ == 0)
{
lean_inc(v___x_2514_);
v___y_2516_ = v___x_2514_;
goto v___jp_2515_;
}
else
{
v___y_2516_ = v___x_2511_;
goto v___jp_2515_;
}
v___jp_2515_:
{
uint8_t v___x_2517_; 
v___x_2517_ = lean_nat_dec_le(v___y_2516_, v___x_2514_);
if (v___x_2517_ == 0)
{
lean_dec(v___x_2514_);
lean_inc(v___y_2516_);
v___y_2508_ = v___y_2516_;
v___y_2509_ = v___y_2516_;
goto v___jp_2507_;
}
else
{
v___y_2508_ = v___y_2516_;
v___y_2509_ = v___x_2514_;
goto v___jp_2507_;
}
}
}
else
{
v___y_2491_ = v___x_2505_;
goto v___jp_2490_;
}
v___jp_2507_:
{
lean_object* v___x_2510_; 
v___x_2510_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v___x_2506_, v___x_2505_, v___y_2508_, v___y_2509_);
lean_dec(v___y_2509_);
v___y_2491_ = v___x_2510_;
goto v___jp_2490_;
}
}
else
{
lean_object* v___x_2519_; 
v___x_2519_ = l_Lean_MessageData_nil;
v_a_2475_ = v___x_2519_;
goto v___jp_2474_;
}
}
v___jp_2452_:
{
lean_object* v___x_2458_; 
if (v_isShared_2451_ == 0)
{
lean_ctor_set_tag(v___x_2450_, 7);
lean_ctor_set(v___x_2450_, 1, v___y_2456_);
lean_ctor_set(v___x_2450_, 0, v___y_2454_);
v___x_2458_ = v___x_2450_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___y_2454_);
lean_ctor_set(v_reuseFailAlloc_2473_, 1, v___y_2456_);
v___x_2458_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
if (lean_obj_tag(v_snd_2448_) == 0)
{
lean_object* v___x_2459_; 
lean_del_object(v___x_2445_);
v___x_2459_ = l_Lean_MessageData_nil;
v___y_2430_ = v___y_2453_;
v___y_2431_ = v___x_2458_;
v___y_2432_ = v___y_2455_;
v___y_2433_ = v___x_2459_;
goto v___jp_2429_;
}
else
{
lean_object* v_val_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2471_; 
v_val_2460_ = lean_ctor_get(v_snd_2448_, 0);
lean_inc_n(v_val_2460_, 2);
lean_dec_ref(v_snd_2448_);
v___x_2461_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2462_ = lean_unsigned_to_nat(0u);
v___x_2463_ = lean_string_utf8_byte_size(v_val_2460_);
v___x_2464_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2464_, 0, v_val_2460_);
lean_ctor_set(v___x_2464_, 1, v___x_2462_);
lean_ctor_set(v___x_2464_, 2, v___x_2463_);
v___x_2465_ = l_String_Slice_splitToSubslice___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__4(v___x_2464_);
v___x_2466_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__0));
v___x_2467_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_2460_, v___x_2464_, v___x_2463_, v___x_2465_, v___x_2466_);
lean_dec_ref(v___x_2464_);
lean_dec(v_val_2460_);
v___x_2468_ = lean_array_to_list(v___x_2467_);
v___x_2469_ = l_Lean_MessageData_joinSep(v___x_2468_, v___x_2461_);
if (v_isShared_2446_ == 0)
{
lean_ctor_set_tag(v___x_2445_, 7);
lean_ctor_set(v___x_2445_, 1, v___x_2469_);
lean_ctor_set(v___x_2445_, 0, v___x_2461_);
v___x_2471_ = v___x_2445_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2461_);
lean_ctor_set(v_reuseFailAlloc_2472_, 1, v___x_2469_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
v___y_2430_ = v___y_2453_;
v___y_2431_ = v___x_2458_;
v___y_2432_ = v___y_2455_;
v___y_2433_ = v___x_2471_;
goto v___jp_2429_;
}
}
}
}
v___jp_2474_:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; uint8_t v___x_2481_; lean_object* v___x_2482_; uint8_t v___x_2483_; 
v___x_2476_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__2);
v___x_2477_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12, &l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12_once, _init_l_Lean_Elab_Tactic_Doc_elabTacticExtension___closed__12);
lean_inc(v_fst_2443_);
v___x_2478_ = l_Lean_MessageData_ofName(v_fst_2443_);
v___x_2479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2477_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
v___x_2480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
lean_ctor_set(v___x_2480_, 1, v___x_2477_);
v___x_2481_ = 1;
v___x_2482_ = l_Lean_Name_toString(v_fst_2443_, v___x_2481_);
v___x_2483_ = lean_string_dec_eq(v___x_2482_, v_fst_2447_);
lean_dec_ref(v___x_2482_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2484_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__4);
v___x_2485_ = l_Lean_stringToMessageData(v_fst_2447_);
v___x_2486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2484_);
lean_ctor_set(v___x_2486_, 1, v___x_2485_);
v___x_2487_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__6);
v___x_2488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2486_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v___y_2453_ = v___x_2476_;
v___y_2454_ = v___x_2480_;
v___y_2455_ = v_a_2475_;
v___y_2456_ = v___x_2488_;
goto v___jp_2452_;
}
else
{
lean_object* v___x_2489_; 
lean_dec(v_fst_2447_);
v___x_2489_ = l_Lean_MessageData_nil;
v___y_2453_ = v___x_2476_;
v___y_2454_ = v___x_2480_;
v___y_2455_ = v_a_2475_;
v___y_2456_ = v___x_2489_;
goto v___jp_2452_;
}
}
v___jp_2490_:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2492_ = lean_array_to_list(v___y_2491_);
v___x_2493_ = lean_box(0);
v___x_2494_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__7(v_a_2415_, v___x_2492_, v___x_2493_, v___y_2419_, v___y_2420_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2495_);
lean_dec_ref(v___x_2494_);
v___x_2496_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_2497_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9, &l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9_once, _init_l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___closed__9);
v___x_2498_ = l_Lean_MessageData_joinSep(v_a_2495_, v___x_2497_);
v___x_2499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2496_);
lean_ctor_set(v___x_2499_, 1, v___x_2498_);
v_a_2475_ = v___x_2499_;
goto v___jp_2474_;
}
else
{
lean_del_object(v___x_2450_);
lean_dec(v_snd_2448_);
lean_dec(v_fst_2447_);
lean_del_object(v___x_2445_);
lean_dec(v_fst_2443_);
lean_del_object(v___x_2427_);
lean_dec(v_tail_2425_);
lean_dec(v_x_2418_);
return v___x_2494_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11___boxed(lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_x_2525_, lean_object* v_x_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_2523_, v_a_2524_, v_x_2525_, v_x_2526_, v___y_2527_, v___y_2528_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec(v_a_2524_);
lean_dec(v_a_2523_);
return v_res_2530_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34___lam__0(uint8_t v___y_2532_, uint8_t v_suppressElabErrors_2533_, lean_object* v_x_2534_){
_start:
{
if (lean_obj_tag(v_x_2534_) == 1)
{
lean_object* v_pre_2535_; 
v_pre_2535_ = lean_ctor_get(v_x_2534_, 0);
if (lean_obj_tag(v_pre_2535_) == 0)
{
lean_object* v_str_2536_; lean_object* v___x_2537_; uint8_t v___x_2538_; 
v_str_2536_ = lean_ctor_get(v_x_2534_, 1);
v___x_2537_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34___lam__0___closed__0));
v___x_2538_ = lean_string_dec_eq(v_str_2536_, v___x_2537_);
if (v___x_2538_ == 0)
{
return v___y_2532_;
}
else
{
return v_suppressElabErrors_2533_;
}
}
else
{
return v___y_2532_;
}
}
else
{
return v___y_2532_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34___lam__0___boxed(lean_object* v___y_2539_, lean_object* v_suppressElabErrors_2540_, lean_object* v_x_2541_){
_start:
{
uint8_t v___y_19919__boxed_2542_; uint8_t v_suppressElabErrors_boxed_2543_; uint8_t v_res_2544_; lean_object* v_r_2545_; 
v___y_19919__boxed_2542_ = lean_unbox(v___y_2539_);
v_suppressElabErrors_boxed_2543_ = lean_unbox(v_suppressElabErrors_2540_);
v_res_2544_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34___lam__0(v___y_19919__boxed_2542_, v_suppressElabErrors_boxed_2543_, v_x_2541_);
lean_dec(v_x_2541_);
v_r_2545_ = lean_box(v_res_2544_);
return v_r_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34(lean_object* v_ref_2546_, lean_object* v_msgData_2547_, uint8_t v_severity_2548_, uint8_t v_isSilent_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; uint8_t v___y_2558_; uint8_t v___y_2559_; lean_object* v___y_2560_; lean_object* v___y_2561_; uint8_t v___y_2617_; uint8_t v___y_2618_; uint8_t v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; uint8_t v___y_2645_; lean_object* v___y_2646_; uint8_t v___y_2647_; uint8_t v___y_2648_; lean_object* v___y_2649_; uint8_t v___y_2653_; uint8_t v___y_2654_; uint8_t v___y_2655_; uint8_t v___x_2670_; uint8_t v___y_2672_; uint8_t v___y_2673_; uint8_t v___y_2674_; uint8_t v___y_2676_; uint8_t v___x_2688_; 
v___x_2670_ = 2;
v___x_2688_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2548_, v___x_2670_);
if (v___x_2688_ == 0)
{
v___y_2676_ = v___x_2688_;
goto v___jp_2675_;
}
else
{
uint8_t v___x_2689_; 
lean_inc_ref(v_msgData_2547_);
v___x_2689_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2547_);
v___y_2676_ = v___x_2689_;
goto v___jp_2675_;
}
v___jp_2553_:
{
lean_object* v___x_2562_; 
v___x_2562_ = l_Lean_Elab_Command_getScope___redArg(v___y_2561_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; lean_object* v___x_2564_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2563_);
lean_dec_ref(v___x_2562_);
v___x_2564_ = l_Lean_Elab_Command_getScope___redArg(v___y_2561_);
if (lean_obj_tag(v___x_2564_) == 0)
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2599_; 
v_a_2565_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2567_ = v___x_2564_;
v_isShared_2568_ = v_isSharedCheck_2599_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2564_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2599_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2569_; lean_object* v_currNamespace_2570_; lean_object* v_openDecls_2571_; lean_object* v_env_2572_; lean_object* v_messages_2573_; lean_object* v_scopes_2574_; lean_object* v_usedQuotCtxts_2575_; lean_object* v_nextMacroScope_2576_; lean_object* v_maxRecDepth_2577_; lean_object* v_ngen_2578_; lean_object* v_auxDeclNGen_2579_; lean_object* v_infoState_2580_; lean_object* v_traceState_2581_; lean_object* v_snapshotTasks_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2598_; 
v___x_2569_ = lean_st_ref_take(v___y_2561_);
v_currNamespace_2570_ = lean_ctor_get(v_a_2563_, 2);
lean_inc(v_currNamespace_2570_);
lean_dec(v_a_2563_);
v_openDecls_2571_ = lean_ctor_get(v_a_2565_, 3);
lean_inc(v_openDecls_2571_);
lean_dec(v_a_2565_);
v_env_2572_ = lean_ctor_get(v___x_2569_, 0);
v_messages_2573_ = lean_ctor_get(v___x_2569_, 1);
v_scopes_2574_ = lean_ctor_get(v___x_2569_, 2);
v_usedQuotCtxts_2575_ = lean_ctor_get(v___x_2569_, 3);
v_nextMacroScope_2576_ = lean_ctor_get(v___x_2569_, 4);
v_maxRecDepth_2577_ = lean_ctor_get(v___x_2569_, 5);
v_ngen_2578_ = lean_ctor_get(v___x_2569_, 6);
v_auxDeclNGen_2579_ = lean_ctor_get(v___x_2569_, 7);
v_infoState_2580_ = lean_ctor_get(v___x_2569_, 8);
v_traceState_2581_ = lean_ctor_get(v___x_2569_, 9);
v_snapshotTasks_2582_ = lean_ctor_get(v___x_2569_, 10);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2584_ = v___x_2569_;
v_isShared_2585_ = v_isSharedCheck_2598_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_snapshotTasks_2582_);
lean_inc(v_traceState_2581_);
lean_inc(v_infoState_2580_);
lean_inc(v_auxDeclNGen_2579_);
lean_inc(v_ngen_2578_);
lean_inc(v_maxRecDepth_2577_);
lean_inc(v_nextMacroScope_2576_);
lean_inc(v_usedQuotCtxts_2575_);
lean_inc(v_scopes_2574_);
lean_inc(v_messages_2573_);
lean_inc(v_env_2572_);
lean_dec(v___x_2569_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2598_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2591_; 
v___x_2586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2586_, 0, v_currNamespace_2570_);
lean_ctor_set(v___x_2586_, 1, v_openDecls_2571_);
v___x_2587_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2586_);
lean_ctor_set(v___x_2587_, 1, v___y_2556_);
lean_inc_ref(v___y_2555_);
lean_inc_ref(v___y_2554_);
v___x_2588_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2588_, 0, v___y_2554_);
lean_ctor_set(v___x_2588_, 1, v___y_2557_);
lean_ctor_set(v___x_2588_, 2, v___y_2560_);
lean_ctor_set(v___x_2588_, 3, v___y_2555_);
lean_ctor_set(v___x_2588_, 4, v___x_2587_);
lean_ctor_set_uint8(v___x_2588_, sizeof(void*)*5, v___y_2558_);
lean_ctor_set_uint8(v___x_2588_, sizeof(void*)*5 + 1, v___y_2559_);
lean_ctor_set_uint8(v___x_2588_, sizeof(void*)*5 + 2, v_isSilent_2549_);
v___x_2589_ = l_Lean_MessageLog_add(v___x_2588_, v_messages_2573_);
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 1, v___x_2589_);
v___x_2591_ = v___x_2584_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_env_2572_);
lean_ctor_set(v_reuseFailAlloc_2597_, 1, v___x_2589_);
lean_ctor_set(v_reuseFailAlloc_2597_, 2, v_scopes_2574_);
lean_ctor_set(v_reuseFailAlloc_2597_, 3, v_usedQuotCtxts_2575_);
lean_ctor_set(v_reuseFailAlloc_2597_, 4, v_nextMacroScope_2576_);
lean_ctor_set(v_reuseFailAlloc_2597_, 5, v_maxRecDepth_2577_);
lean_ctor_set(v_reuseFailAlloc_2597_, 6, v_ngen_2578_);
lean_ctor_set(v_reuseFailAlloc_2597_, 7, v_auxDeclNGen_2579_);
lean_ctor_set(v_reuseFailAlloc_2597_, 8, v_infoState_2580_);
lean_ctor_set(v_reuseFailAlloc_2597_, 9, v_traceState_2581_);
lean_ctor_set(v_reuseFailAlloc_2597_, 10, v_snapshotTasks_2582_);
v___x_2591_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2595_; 
v___x_2592_ = lean_st_ref_set(v___y_2561_, v___x_2591_);
v___x_2593_ = lean_box(0);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v___x_2593_);
v___x_2595_ = v___x_2567_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2593_);
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
else
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2607_; 
lean_dec(v_a_2563_);
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2557_);
lean_dec_ref(v___y_2556_);
v_a_2600_ = lean_ctor_get(v___x_2564_, 0);
v_isSharedCheck_2607_ = !lean_is_exclusive(v___x_2564_);
if (v_isSharedCheck_2607_ == 0)
{
v___x_2602_ = v___x_2564_;
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2564_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2607_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2605_; 
if (v_isShared_2603_ == 0)
{
v___x_2605_ = v___x_2602_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2600_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
}
}
else
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
lean_dec(v___y_2560_);
lean_dec_ref(v___y_2557_);
lean_dec_ref(v___y_2556_);
v_a_2608_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2615_ == 0)
{
v___x_2610_ = v___x_2562_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2562_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_a_2608_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
v___jp_2616_:
{
lean_object* v_fileName_2622_; lean_object* v_fileMap_2623_; uint8_t v_suppressElabErrors_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2643_; 
v_fileName_2622_ = lean_ctor_get(v___y_2550_, 0);
v_fileMap_2623_ = lean_ctor_get(v___y_2550_, 1);
v_suppressElabErrors_2624_ = lean_ctor_get_uint8(v___y_2550_, sizeof(void*)*10);
v___x_2625_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2547_);
v___x_2626_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__0___redArg(v___x_2625_, v___y_2551_);
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2629_ = v___x_2626_;
v_isShared_2630_ = v_isSharedCheck_2643_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2626_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2643_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
lean_inc_ref_n(v_fileMap_2623_, 2);
v___x_2631_ = l_Lean_FileMap_toPosition(v_fileMap_2623_, v___y_2620_);
lean_dec(v___y_2620_);
v___x_2632_ = l_Lean_FileMap_toPosition(v_fileMap_2623_, v___y_2621_);
lean_dec(v___y_2621_);
v___x_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2632_);
v___x_2634_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg___closed__0));
if (v_suppressElabErrors_2624_ == 0)
{
lean_del_object(v___x_2629_);
v___y_2554_ = v_fileName_2622_;
v___y_2555_ = v___x_2634_;
v___y_2556_ = v_a_2627_;
v___y_2557_ = v___x_2631_;
v___y_2558_ = v___y_2618_;
v___y_2559_ = v___y_2619_;
v___y_2560_ = v___x_2633_;
v___y_2561_ = v___y_2551_;
goto v___jp_2553_;
}
else
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___f_2637_; uint8_t v___x_2638_; 
v___x_2635_ = lean_box(v___y_2617_);
v___x_2636_ = lean_box(v_suppressElabErrors_2624_);
v___f_2637_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2637_, 0, v___x_2635_);
lean_closure_set(v___f_2637_, 1, v___x_2636_);
lean_inc(v_a_2627_);
v___x_2638_ = l_Lean_MessageData_hasTag(v___f_2637_, v_a_2627_);
if (v___x_2638_ == 0)
{
lean_object* v___x_2639_; lean_object* v___x_2641_; 
lean_dec_ref(v___x_2633_);
lean_dec_ref(v___x_2631_);
lean_dec(v_a_2627_);
v___x_2639_ = lean_box(0);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 0, v___x_2639_);
v___x_2641_ = v___x_2629_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2639_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
else
{
lean_del_object(v___x_2629_);
v___y_2554_ = v_fileName_2622_;
v___y_2555_ = v___x_2634_;
v___y_2556_ = v_a_2627_;
v___y_2557_ = v___x_2631_;
v___y_2558_ = v___y_2618_;
v___y_2559_ = v___y_2619_;
v___y_2560_ = v___x_2633_;
v___y_2561_ = v___y_2551_;
goto v___jp_2553_;
}
}
}
}
v___jp_2644_:
{
lean_object* v___x_2650_; 
v___x_2650_ = l_Lean_Syntax_getTailPos_x3f(v___y_2646_, v___y_2647_);
lean_dec(v___y_2646_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_inc(v___y_2649_);
v___y_2617_ = v___y_2645_;
v___y_2618_ = v___y_2647_;
v___y_2619_ = v___y_2648_;
v___y_2620_ = v___y_2649_;
v___y_2621_ = v___y_2649_;
goto v___jp_2616_;
}
else
{
lean_object* v_val_2651_; 
v_val_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_val_2651_);
lean_dec_ref(v___x_2650_);
v___y_2617_ = v___y_2645_;
v___y_2618_ = v___y_2647_;
v___y_2619_ = v___y_2648_;
v___y_2620_ = v___y_2649_;
v___y_2621_ = v_val_2651_;
goto v___jp_2616_;
}
}
v___jp_2652_:
{
lean_object* v___x_2656_; 
v___x_2656_ = l_Lean_Elab_Command_getRef___redArg(v___y_2550_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v_ref_2658_; lean_object* v___x_2659_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref(v___x_2656_);
v_ref_2658_ = l_Lean_replaceRef(v_ref_2546_, v_a_2657_);
lean_dec(v_a_2657_);
v___x_2659_ = l_Lean_Syntax_getPos_x3f(v_ref_2658_, v___y_2654_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v___x_2660_; 
v___x_2660_ = lean_unsigned_to_nat(0u);
v___y_2645_ = v___y_2653_;
v___y_2646_ = v_ref_2658_;
v___y_2647_ = v___y_2654_;
v___y_2648_ = v___y_2655_;
v___y_2649_ = v___x_2660_;
goto v___jp_2644_;
}
else
{
lean_object* v_val_2661_; 
v_val_2661_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_val_2661_);
lean_dec_ref(v___x_2659_);
v___y_2645_ = v___y_2653_;
v___y_2646_ = v_ref_2658_;
v___y_2647_ = v___y_2654_;
v___y_2648_ = v___y_2655_;
v___y_2649_ = v_val_2661_;
goto v___jp_2644_;
}
}
else
{
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2669_; 
lean_dec_ref(v_msgData_2547_);
v_a_2662_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2664_ = v___x_2656_;
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2656_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2667_; 
if (v_isShared_2665_ == 0)
{
v___x_2667_ = v___x_2664_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_a_2662_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
}
v___jp_2671_:
{
if (v___y_2674_ == 0)
{
v___y_2653_ = v___y_2672_;
v___y_2654_ = v___y_2673_;
v___y_2655_ = v_severity_2548_;
goto v___jp_2652_;
}
else
{
v___y_2653_ = v___y_2672_;
v___y_2654_ = v___y_2673_;
v___y_2655_ = v___x_2670_;
goto v___jp_2652_;
}
}
v___jp_2675_:
{
if (v___y_2676_ == 0)
{
lean_object* v___x_2677_; lean_object* v_scopes_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v_opts_2681_; uint8_t v___x_2682_; uint8_t v___x_2683_; 
v___x_2677_ = lean_st_ref_get(v___y_2551_);
v_scopes_2678_ = lean_ctor_get(v___x_2677_, 2);
lean_inc(v_scopes_2678_);
lean_dec(v___x_2677_);
v___x_2679_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_2680_ = l_List_head_x21___redArg(v___x_2679_, v_scopes_2678_);
lean_dec(v_scopes_2678_);
v_opts_2681_ = lean_ctor_get(v___x_2680_, 1);
lean_inc_ref(v_opts_2681_);
lean_dec(v___x_2680_);
v___x_2682_ = 1;
v___x_2683_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2548_, v___x_2682_);
if (v___x_2683_ == 0)
{
lean_dec_ref(v_opts_2681_);
v___y_2672_ = v___y_2676_;
v___y_2673_ = v___y_2676_;
v___y_2674_ = v___x_2683_;
goto v___jp_2671_;
}
else
{
lean_object* v___x_2684_; uint8_t v___x_2685_; 
v___x_2684_ = l_Lean_warningAsError;
v___x_2685_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__2(v_opts_2681_, v___x_2684_);
lean_dec_ref(v_opts_2681_);
v___y_2672_ = v___y_2676_;
v___y_2673_ = v___y_2676_;
v___y_2674_ = v___x_2685_;
goto v___jp_2671_;
}
}
else
{
lean_object* v___x_2686_; lean_object* v___x_2687_; 
lean_dec_ref(v_msgData_2547_);
v___x_2686_ = lean_box(0);
v___x_2687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2686_);
return v___x_2687_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34___boxed(lean_object* v_ref_2690_, lean_object* v_msgData_2691_, lean_object* v_severity_2692_, lean_object* v_isSilent_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_){
_start:
{
uint8_t v_severity_boxed_2697_; uint8_t v_isSilent_boxed_2698_; lean_object* v_res_2699_; 
v_severity_boxed_2697_ = lean_unbox(v_severity_2692_);
v_isSilent_boxed_2698_ = lean_unbox(v_isSilent_2693_);
v_res_2699_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34(v_ref_2690_, v_msgData_2691_, v_severity_boxed_2697_, v_isSilent_boxed_2698_, v___y_2694_, v___y_2695_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v_ref_2690_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28(lean_object* v_msgData_2700_, uint8_t v_severity_2701_, uint8_t v_isSilent_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
lean_object* v___x_2706_; 
v___x_2706_ = l_Lean_Elab_Command_getRef___redArg(v___y_2703_);
if (lean_obj_tag(v___x_2706_) == 0)
{
lean_object* v_a_2707_; lean_object* v___x_2708_; 
v_a_2707_ = lean_ctor_get(v___x_2706_, 0);
lean_inc(v_a_2707_);
lean_dec_ref(v___x_2706_);
v___x_2708_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28_spec__34(v_a_2707_, v_msgData_2700_, v_severity_2701_, v_isSilent_2702_, v___y_2703_, v___y_2704_);
lean_dec(v_a_2707_);
return v___x_2708_;
}
else
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2716_; 
lean_dec_ref(v_msgData_2700_);
v_a_2709_ = lean_ctor_get(v___x_2706_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2706_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2711_ = v___x_2706_;
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2706_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_a_2709_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28___boxed(lean_object* v_msgData_2717_, lean_object* v_severity_2718_, lean_object* v_isSilent_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
uint8_t v_severity_boxed_2723_; uint8_t v_isSilent_boxed_2724_; lean_object* v_res_2725_; 
v_severity_boxed_2723_ = lean_unbox(v_severity_2718_);
v_isSilent_boxed_2724_ = lean_unbox(v_isSilent_2719_);
v_res_2725_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28(v_msgData_2717_, v_severity_boxed_2723_, v_isSilent_boxed_2724_, v___y_2720_, v___y_2721_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(lean_object* v_msgData_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
uint8_t v___x_2730_; uint8_t v___x_2731_; lean_object* v___x_2732_; 
v___x_2730_ = 0;
v___x_2731_ = 0;
v___x_2732_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12_spec__28(v_msgData_2726_, v___x_2730_, v___x_2731_, v___y_2727_, v___y_2728_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12___boxed(lean_object* v_msgData_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v_msgData_2733_, v___y_2734_, v___y_2735_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24_spec__29___redArg(lean_object* v_hi_2738_, lean_object* v_pivot_2739_, lean_object* v_as_2740_, lean_object* v_i_2741_, lean_object* v_k_2742_){
_start:
{
uint8_t v___x_2743_; 
v___x_2743_ = lean_nat_dec_lt(v_k_2742_, v_hi_2738_);
if (v___x_2743_ == 0)
{
lean_object* v___x_2744_; lean_object* v___x_2745_; 
lean_dec(v_k_2742_);
lean_dec_ref(v_pivot_2739_);
v___x_2744_ = lean_array_fswap(v_as_2740_, v_i_2741_, v_hi_2738_);
v___x_2745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2745_, 0, v_i_2741_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
return v___x_2745_;
}
else
{
lean_object* v___x_2746_; lean_object* v_fst_2747_; lean_object* v_fst_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; uint8_t v___x_2751_; 
v___x_2746_ = lean_array_fget_borrowed(v_as_2740_, v_k_2742_);
v_fst_2747_ = lean_ctor_get(v___x_2746_, 0);
v_fst_2748_ = lean_ctor_get(v_pivot_2739_, 0);
lean_inc(v_fst_2747_);
v___x_2749_ = l_Lean_Name_toString(v_fst_2747_, v___x_2743_);
lean_inc(v_fst_2748_);
v___x_2750_ = l_Lean_Name_toString(v_fst_2748_, v___x_2743_);
v___x_2751_ = lean_string_dec_lt(v___x_2749_, v___x_2750_);
lean_dec_ref(v___x_2750_);
lean_dec_ref(v___x_2749_);
if (v___x_2751_ == 0)
{
lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2752_ = lean_unsigned_to_nat(1u);
v___x_2753_ = lean_nat_add(v_k_2742_, v___x_2752_);
lean_dec(v_k_2742_);
v_k_2742_ = v___x_2753_;
goto _start;
}
else
{
lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2755_ = lean_array_fswap(v_as_2740_, v_i_2741_, v_k_2742_);
v___x_2756_ = lean_unsigned_to_nat(1u);
v___x_2757_ = lean_nat_add(v_i_2741_, v___x_2756_);
lean_dec(v_i_2741_);
v___x_2758_ = lean_nat_add(v_k_2742_, v___x_2756_);
lean_dec(v_k_2742_);
v_as_2740_ = v___x_2755_;
v_i_2741_ = v___x_2757_;
v_k_2742_ = v___x_2758_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24_spec__29___redArg___boxed(lean_object* v_hi_2760_, lean_object* v_pivot_2761_, lean_object* v_as_2762_, lean_object* v_i_2763_, lean_object* v_k_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24_spec__29___redArg(v_hi_2760_, v_pivot_2761_, v_as_2762_, v_i_2763_, v_k_2764_);
lean_dec(v_hi_2760_);
return v_res_2765_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg___lam__0(uint8_t v___x_2766_, lean_object* v_x1_2767_, lean_object* v_x2_2768_){
_start:
{
lean_object* v_fst_2769_; lean_object* v_fst_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; uint8_t v___x_2773_; 
v_fst_2769_ = lean_ctor_get(v_x1_2767_, 0);
lean_inc(v_fst_2769_);
lean_dec_ref(v_x1_2767_);
v_fst_2770_ = lean_ctor_get(v_x2_2768_, 0);
lean_inc(v_fst_2770_);
lean_dec_ref(v_x2_2768_);
v___x_2771_ = l_Lean_Name_toString(v_fst_2769_, v___x_2766_);
v___x_2772_ = l_Lean_Name_toString(v_fst_2770_, v___x_2766_);
v___x_2773_ = lean_string_dec_lt(v___x_2771_, v___x_2772_);
lean_dec_ref(v___x_2772_);
lean_dec_ref(v___x_2771_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg___lam__0___boxed(lean_object* v___x_2774_, lean_object* v_x1_2775_, lean_object* v_x2_2776_){
_start:
{
uint8_t v___x_20261__boxed_2777_; uint8_t v_res_2778_; lean_object* v_r_2779_; 
v___x_20261__boxed_2777_ = lean_unbox(v___x_2774_);
v_res_2778_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg___lam__0(v___x_20261__boxed_2777_, v_x1_2775_, v_x2_2776_);
v_r_2779_ = lean_box(v_res_2778_);
return v_r_2779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg(lean_object* v_n_2780_, lean_object* v_as_2781_, lean_object* v_lo_2782_, lean_object* v_hi_2783_){
_start:
{
lean_object* v___y_2785_; uint8_t v___x_2795_; 
v___x_2795_ = lean_nat_dec_lt(v_lo_2782_, v_hi_2783_);
if (v___x_2795_ == 0)
{
lean_dec(v_lo_2782_);
return v_as_2781_;
}
else
{
lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v_mid_2798_; lean_object* v___y_2800_; lean_object* v___y_2806_; lean_object* v___x_2811_; lean_object* v___x_2812_; uint8_t v___x_2813_; 
v___x_2796_ = lean_nat_add(v_lo_2782_, v_hi_2783_);
v___x_2797_ = lean_unsigned_to_nat(1u);
v_mid_2798_ = lean_nat_shiftr(v___x_2796_, v___x_2797_);
lean_dec(v___x_2796_);
v___x_2811_ = lean_array_fget_borrowed(v_as_2781_, v_mid_2798_);
v___x_2812_ = lean_array_fget_borrowed(v_as_2781_, v_lo_2782_);
lean_inc(v___x_2812_);
lean_inc(v___x_2811_);
v___x_2813_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg___lam__0(v___x_2795_, v___x_2811_, v___x_2812_);
if (v___x_2813_ == 0)
{
v___y_2806_ = v_as_2781_;
goto v___jp_2805_;
}
else
{
lean_object* v___x_2814_; 
v___x_2814_ = lean_array_fswap(v_as_2781_, v_lo_2782_, v_mid_2798_);
v___y_2806_ = v___x_2814_;
goto v___jp_2805_;
}
v___jp_2799_:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; uint8_t v___x_2803_; 
v___x_2801_ = lean_array_fget_borrowed(v___y_2800_, v_mid_2798_);
v___x_2802_ = lean_array_fget_borrowed(v___y_2800_, v_hi_2783_);
lean_inc(v___x_2802_);
lean_inc(v___x_2801_);
v___x_2803_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg___lam__0(v___x_2795_, v___x_2801_, v___x_2802_);
if (v___x_2803_ == 0)
{
lean_dec(v_mid_2798_);
v___y_2785_ = v___y_2800_;
goto v___jp_2784_;
}
else
{
lean_object* v___x_2804_; 
v___x_2804_ = lean_array_fswap(v___y_2800_, v_mid_2798_, v_hi_2783_);
lean_dec(v_mid_2798_);
v___y_2785_ = v___x_2804_;
goto v___jp_2784_;
}
}
v___jp_2805_:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; uint8_t v___x_2809_; 
v___x_2807_ = lean_array_fget_borrowed(v___y_2806_, v_hi_2783_);
v___x_2808_ = lean_array_fget_borrowed(v___y_2806_, v_lo_2782_);
lean_inc(v___x_2808_);
lean_inc(v___x_2807_);
v___x_2809_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg___lam__0(v___x_2795_, v___x_2807_, v___x_2808_);
if (v___x_2809_ == 0)
{
v___y_2800_ = v___y_2806_;
goto v___jp_2799_;
}
else
{
lean_object* v___x_2810_; 
v___x_2810_ = lean_array_fswap(v___y_2806_, v_lo_2782_, v_hi_2783_);
v___y_2800_ = v___x_2810_;
goto v___jp_2799_;
}
}
}
v___jp_2784_:
{
lean_object* v_pivot_2786_; lean_object* v___x_2787_; lean_object* v_fst_2788_; lean_object* v_snd_2789_; uint8_t v___x_2790_; 
v_pivot_2786_ = lean_array_fget(v___y_2785_, v_hi_2783_);
lean_inc_n(v_lo_2782_, 2);
v___x_2787_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24_spec__29___redArg(v_hi_2783_, v_pivot_2786_, v___y_2785_, v_lo_2782_, v_lo_2782_);
v_fst_2788_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_fst_2788_);
v_snd_2789_ = lean_ctor_get(v___x_2787_, 1);
lean_inc(v_snd_2789_);
lean_dec_ref(v___x_2787_);
v___x_2790_ = lean_nat_dec_le(v_hi_2783_, v_fst_2788_);
if (v___x_2790_ == 0)
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2791_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg(v_n_2780_, v_snd_2789_, v_lo_2782_, v_fst_2788_);
v___x_2792_ = lean_unsigned_to_nat(1u);
v___x_2793_ = lean_nat_add(v_fst_2788_, v___x_2792_);
lean_dec(v_fst_2788_);
v_as_2781_ = v___x_2791_;
v_lo_2782_ = v___x_2793_;
goto _start;
}
else
{
lean_dec(v_fst_2788_);
lean_dec(v_lo_2782_);
return v_snd_2789_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg___boxed(lean_object* v_n_2815_, lean_object* v_as_2816_, lean_object* v_lo_2817_, lean_object* v_hi_2818_){
_start:
{
lean_object* v_res_2819_; 
v_res_2819_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg(v_n_2815_, v_as_2816_, v_lo_2817_, v_hi_2818_);
lean_dec(v_hi_2818_);
lean_dec(v_n_2815_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23_spec__27(lean_object* v_init_2820_, lean_object* v_x_2821_){
_start:
{
if (lean_obj_tag(v_x_2821_) == 0)
{
lean_object* v_k_2822_; lean_object* v_v_2823_; lean_object* v_l_2824_; lean_object* v_r_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
v_k_2822_ = lean_ctor_get(v_x_2821_, 1);
v_v_2823_ = lean_ctor_get(v_x_2821_, 2);
v_l_2824_ = lean_ctor_get(v_x_2821_, 3);
v_r_2825_ = lean_ctor_get(v_x_2821_, 4);
v___x_2826_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23_spec__27(v_init_2820_, v_l_2824_);
lean_inc(v_v_2823_);
lean_inc(v_k_2822_);
v___x_2827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2827_, 0, v_k_2822_);
lean_ctor_set(v___x_2827_, 1, v_v_2823_);
v___x_2828_ = lean_array_push(v___x_2826_, v___x_2827_);
v_init_2820_ = v___x_2828_;
v_x_2821_ = v_r_2825_;
goto _start;
}
else
{
return v_init_2820_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23_spec__27___boxed(lean_object* v_init_2830_, lean_object* v_x_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23_spec__27(v_init_2830_, v_x_2831_);
lean_dec(v_x_2831_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__25___redArg(lean_object* v_init_2833_, lean_object* v_x_2834_){
_start:
{
if (lean_obj_tag(v_x_2834_) == 0)
{
lean_object* v_k_2836_; lean_object* v_v_2837_; lean_object* v_l_2838_; lean_object* v_r_2839_; lean_object* v___x_2840_; lean_object* v_a_2841_; lean_object* v_a_2842_; lean_object* v___x_2843_; 
v_k_2836_ = lean_ctor_get(v_x_2834_, 1);
lean_inc(v_k_2836_);
v_v_2837_ = lean_ctor_get(v_x_2834_, 2);
lean_inc(v_v_2837_);
v_l_2838_ = lean_ctor_get(v_x_2834_, 3);
lean_inc(v_l_2838_);
v_r_2839_ = lean_ctor_get(v_x_2834_, 4);
lean_inc(v_r_2839_);
lean_dec_ref(v_x_2834_);
v___x_2840_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__25___redArg(v_init_2833_, v_l_2838_);
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
lean_inc(v_a_2841_);
lean_dec_ref(v___x_2840_);
v_a_2842_ = lean_ctor_get(v_a_2841_, 0);
lean_inc(v_a_2842_);
lean_dec(v_a_2841_);
v___x_2843_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_2836_, v_v_2837_, v_a_2842_);
v_init_2833_ = v___x_2843_;
v_x_2834_ = v_r_2839_;
goto _start;
}
else
{
lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2845_, 0, v_init_2833_);
v___x_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2845_);
return v___x_2846_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__25___redArg___boxed(lean_object* v_init_2847_, lean_object* v_x_2848_, lean_object* v___y_2849_){
_start:
{
lean_object* v_res_2850_; 
v_res_2850_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__25___redArg(v_init_2847_, v_x_2848_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___redArg(lean_object* v_as_2851_, size_t v_sz_2852_, size_t v_i_2853_, lean_object* v_b_2854_){
_start:
{
uint8_t v___x_2856_; 
v___x_2856_ = lean_usize_dec_lt(v_i_2853_, v_sz_2852_);
if (v___x_2856_ == 0)
{
lean_object* v___x_2857_; 
v___x_2857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2857_, 0, v_b_2854_);
return v___x_2857_;
}
else
{
lean_object* v_a_2858_; lean_object* v_fst_2859_; lean_object* v_snd_2860_; lean_object* v_found_2861_; size_t v___x_2862_; size_t v___x_2863_; 
v_a_2858_ = lean_array_uget_borrowed(v_as_2851_, v_i_2853_);
v_fst_2859_ = lean_ctor_get(v_a_2858_, 0);
v_snd_2860_ = lean_ctor_get(v_a_2858_, 1);
lean_inc(v_snd_2860_);
lean_inc(v_fst_2859_);
v_found_2861_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2859_, v_snd_2860_, v_b_2854_);
v___x_2862_ = ((size_t)1ULL);
v___x_2863_ = lean_usize_add(v_i_2853_, v___x_2862_);
v_i_2853_ = v___x_2863_;
v_b_2854_ = v_found_2861_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___redArg___boxed(lean_object* v_as_2865_, lean_object* v_sz_2866_, lean_object* v_i_2867_, lean_object* v_b_2868_, lean_object* v___y_2869_){
_start:
{
size_t v_sz_boxed_2870_; size_t v_i_boxed_2871_; lean_object* v_res_2872_; 
v_sz_boxed_2870_ = lean_unbox_usize(v_sz_2866_);
lean_dec(v_sz_2866_);
v_i_boxed_2871_ = lean_unbox_usize(v_i_2867_);
lean_dec(v_i_2867_);
v_res_2872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___redArg(v_as_2865_, v_sz_boxed_2870_, v_i_boxed_2871_, v_b_2868_);
lean_dec_ref(v_as_2865_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(lean_object* v_as_2873_, size_t v_sz_2874_, size_t v_i_2875_, lean_object* v_b_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
uint8_t v___x_2880_; 
v___x_2880_ = lean_usize_dec_lt(v_i_2875_, v_sz_2874_);
if (v___x_2880_ == 0)
{
lean_object* v___x_2881_; 
v___x_2881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2881_, 0, v_b_2876_);
return v___x_2881_;
}
else
{
lean_object* v_a_2882_; size_t v_sz_2883_; size_t v___x_2884_; lean_object* v___x_2885_; 
v_a_2882_ = lean_array_uget_borrowed(v_as_2873_, v_i_2875_);
v_sz_2883_ = lean_array_size(v_a_2882_);
v___x_2884_ = ((size_t)0ULL);
v___x_2885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___redArg(v_a_2882_, v_sz_2883_, v___x_2884_, v_b_2876_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v_a_2886_; size_t v___x_2887_; size_t v___x_2888_; 
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_a_2886_);
lean_dec_ref(v___x_2885_);
v___x_2887_ = ((size_t)1ULL);
v___x_2888_ = lean_usize_add(v_i_2875_, v___x_2887_);
v_i_2875_ = v___x_2888_;
v_b_2876_ = v_a_2886_;
goto _start;
}
else
{
return v___x_2885_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22___boxed(lean_object* v_as_2890_, lean_object* v_sz_2891_, lean_object* v_i_2892_, lean_object* v_b_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_){
_start:
{
size_t v_sz_boxed_2897_; size_t v_i_boxed_2898_; lean_object* v_res_2899_; 
v_sz_boxed_2897_ = lean_unbox_usize(v_sz_2891_);
lean_dec(v_sz_2891_);
v_i_boxed_2898_ = lean_unbox_usize(v_i_2892_);
lean_dec(v_i_2892_);
v_res_2899_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(v_as_2890_, v_sz_boxed_2897_, v_i_boxed_2898_, v_b_2893_, v___y_2894_, v___y_2895_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
lean_dec_ref(v_as_2890_);
return v_res_2899_;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0(void){
_start:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2900_ = lean_box(1);
v___x_2901_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2900_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(lean_object* v___y_2904_, lean_object* v___y_2905_){
_start:
{
lean_object* v___y_2908_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___x_2923_; lean_object* v_env_2924_; lean_object* v___x_2925_; lean_object* v_toEnvExtension_2926_; lean_object* v_asyncMode_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v_a_2933_; lean_object* v_a_2935_; lean_object* v_a_2958_; 
v___x_2923_ = lean_st_ref_get(v___y_2905_);
v_env_2924_ = lean_ctor_get(v___x_2923_, 0);
lean_inc_ref_n(v_env_2924_, 2);
lean_dec(v___x_2923_);
v___x_2925_ = l_Lean_Parser_Tactic_Doc_knownTacticTagExt;
v_toEnvExtension_2926_ = lean_ctor_get(v___x_2925_, 0);
v_asyncMode_2927_ = lean_ctor_get(v_toEnvExtension_2926_, 2);
v___x_2928_ = lean_box(1);
v___x_2929_ = lean_obj_once(&l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0, &l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0_once, _init_l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__0);
v___x_2930_ = lean_box(0);
v___x_2931_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2928_, v___x_2925_, v_env_2924_, v_asyncMode_2927_, v___x_2930_);
v___x_2932_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__25___redArg(v___x_2928_, v___x_2931_);
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
lean_inc(v_a_2933_);
lean_dec_ref(v___x_2932_);
v_a_2958_ = lean_ctor_get(v_a_2933_, 0);
lean_inc(v_a_2958_);
lean_dec(v_a_2933_);
v_a_2935_ = v_a_2958_;
goto v___jp_2934_;
v___jp_2907_:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; 
v___x_2909_ = lean_array_to_list(v___y_2908_);
v___x_2910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2909_);
return v___x_2910_;
}
v___jp_2911_:
{
lean_object* v___x_2916_; 
v___x_2916_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg(v___y_2914_, v___y_2913_, v___y_2912_, v___y_2915_);
lean_dec(v___y_2915_);
lean_dec(v___y_2914_);
v___y_2908_ = v___x_2916_;
goto v___jp_2907_;
}
v___jp_2917_:
{
uint8_t v___x_2922_; 
v___x_2922_ = lean_nat_dec_le(v___y_2921_, v___y_2918_);
if (v___x_2922_ == 0)
{
lean_dec(v___y_2918_);
lean_inc(v___y_2921_);
v___y_2912_ = v___y_2921_;
v___y_2913_ = v___y_2919_;
v___y_2914_ = v___y_2920_;
v___y_2915_ = v___y_2921_;
goto v___jp_2911_;
}
else
{
v___y_2912_ = v___y_2921_;
v___y_2913_ = v___y_2919_;
v___y_2914_ = v___y_2920_;
v___y_2915_ = v___y_2918_;
goto v___jp_2911_;
}
}
v___jp_2934_:
{
lean_object* v___x_2936_; lean_object* v_importedEntries_2937_; size_t v_sz_2938_; size_t v___x_2939_; lean_object* v___x_2940_; 
v___x_2936_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_2929_, v_toEnvExtension_2926_, v_env_2924_, v_asyncMode_2927_, v___x_2930_);
v_importedEntries_2937_ = lean_ctor_get(v___x_2936_, 0);
lean_inc_ref(v_importedEntries_2937_);
lean_dec(v___x_2936_);
v_sz_2938_ = lean_array_size(v_importedEntries_2937_);
v___x_2939_ = ((size_t)0ULL);
v___x_2940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__22(v_importedEntries_2937_, v_sz_2938_, v___x_2939_, v_a_2935_, v___y_2904_, v___y_2905_);
lean_dec_ref(v_importedEntries_2937_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v_arr_2944_; lean_object* v___x_2945_; uint8_t v___x_2946_; 
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
lean_inc(v_a_2941_);
lean_dec_ref(v___x_2940_);
v___x_2942_ = lean_unsigned_to_nat(0u);
v___x_2943_ = ((lean_object*)(l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___closed__1));
v_arr_2944_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23_spec__27(v___x_2943_, v_a_2941_);
lean_dec(v_a_2941_);
v___x_2945_ = lean_array_get_size(v_arr_2944_);
v___x_2946_ = lean_nat_dec_eq(v___x_2945_, v___x_2942_);
if (v___x_2946_ == 0)
{
lean_object* v___x_2947_; lean_object* v___x_2948_; uint8_t v___x_2949_; 
v___x_2947_ = lean_unsigned_to_nat(1u);
v___x_2948_ = lean_nat_sub(v___x_2945_, v___x_2947_);
v___x_2949_ = lean_nat_dec_le(v___x_2942_, v___x_2948_);
if (v___x_2949_ == 0)
{
lean_inc(v___x_2948_);
v___y_2918_ = v___x_2948_;
v___y_2919_ = v_arr_2944_;
v___y_2920_ = v___x_2945_;
v___y_2921_ = v___x_2948_;
goto v___jp_2917_;
}
else
{
v___y_2918_ = v___x_2948_;
v___y_2919_ = v_arr_2944_;
v___y_2920_ = v___x_2945_;
v___y_2921_ = v___x_2942_;
goto v___jp_2917_;
}
}
else
{
v___y_2908_ = v_arr_2944_;
goto v___jp_2907_;
}
}
else
{
lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2957_; 
v_a_2950_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2952_ = v___x_2940_;
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_dec(v___x_2940_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2955_; 
if (v_isShared_2953_ == 0)
{
v___x_2955_ = v___x_2952_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_a_2950_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
return v___x_2955_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10___boxed(lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v___y_2959_, v___y_2960_);
lean_dec(v___y_2960_);
lean_dec_ref(v___y_2959_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(lean_object* v_t_2963_, lean_object* v_k_2964_, lean_object* v_fallback_2965_){
_start:
{
if (lean_obj_tag(v_t_2963_) == 0)
{
lean_object* v_k_2966_; lean_object* v_v_2967_; lean_object* v_l_2968_; lean_object* v_r_2969_; uint8_t v___x_2970_; 
v_k_2966_ = lean_ctor_get(v_t_2963_, 1);
v_v_2967_ = lean_ctor_get(v_t_2963_, 2);
v_l_2968_ = lean_ctor_get(v_t_2963_, 3);
v_r_2969_ = lean_ctor_get(v_t_2963_, 4);
v___x_2970_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2964_, v_k_2966_);
switch(v___x_2970_)
{
case 0:
{
v_t_2963_ = v_l_2968_;
goto _start;
}
case 1:
{
lean_inc(v_v_2967_);
return v_v_2967_;
}
default: 
{
v_t_2963_ = v_r_2969_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_2965_);
return v_fallback_2965_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg___boxed(lean_object* v_t_2973_, lean_object* v_k_2974_, lean_object* v_fallback_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_2973_, v_k_2974_, v_fallback_2975_);
lean_dec(v_fallback_2975_);
lean_dec(v_k_2974_);
lean_dec(v_t_2973_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(lean_object* v_as_2977_, size_t v_sz_2978_, size_t v_i_2979_, lean_object* v_b_2980_){
_start:
{
uint8_t v___x_2982_; 
v___x_2982_ = lean_usize_dec_lt(v_i_2979_, v_sz_2978_);
if (v___x_2982_ == 0)
{
lean_object* v___x_2983_; 
v___x_2983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2983_, 0, v_b_2980_);
return v___x_2983_;
}
else
{
lean_object* v_a_2984_; lean_object* v_fst_2985_; lean_object* v_snd_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; size_t v___x_2991_; size_t v___x_2992_; 
v_a_2984_ = lean_array_uget_borrowed(v_as_2977_, v_i_2979_);
v_fst_2985_ = lean_ctor_get(v_a_2984_, 0);
v_snd_2986_ = lean_ctor_get(v_a_2984_, 1);
v___x_2987_ = l_Lean_NameSet_empty;
v___x_2988_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_2980_, v_snd_2986_, v___x_2987_);
lean_inc(v_fst_2985_);
v___x_2989_ = l_Lean_NameSet_insert(v___x_2988_, v_fst_2985_);
lean_inc(v_snd_2986_);
v___x_2990_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_snd_2986_, v___x_2989_, v_b_2980_);
v___x_2991_ = ((size_t)1ULL);
v___x_2992_ = lean_usize_add(v_i_2979_, v___x_2991_);
v_i_2979_ = v___x_2992_;
v_b_2980_ = v___x_2990_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg___boxed(lean_object* v_as_2994_, lean_object* v_sz_2995_, lean_object* v_i_2996_, lean_object* v_b_2997_, lean_object* v___y_2998_){
_start:
{
size_t v_sz_boxed_2999_; size_t v_i_boxed_3000_; lean_object* v_res_3001_; 
v_sz_boxed_2999_ = lean_unbox_usize(v_sz_2995_);
lean_dec(v_sz_2995_);
v_i_boxed_3000_ = lean_unbox_usize(v_i_2996_);
lean_dec(v_i_2996_);
v_res_3001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_2994_, v_sz_boxed_2999_, v_i_boxed_3000_, v_b_2997_);
lean_dec_ref(v_as_2994_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(lean_object* v_as_3002_, size_t v_sz_3003_, size_t v_i_3004_, lean_object* v_b_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_){
_start:
{
uint8_t v___x_3009_; 
v___x_3009_ = lean_usize_dec_lt(v_i_3004_, v_sz_3003_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; 
v___x_3010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3010_, 0, v_b_3005_);
return v___x_3010_;
}
else
{
lean_object* v_a_3011_; size_t v_sz_3012_; size_t v___x_3013_; lean_object* v___x_3014_; 
v_a_3011_ = lean_array_uget_borrowed(v_as_3002_, v_i_3004_);
v_sz_3012_ = lean_array_size(v_a_3011_);
v___x_3013_ = ((size_t)0ULL);
v___x_3014_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_a_3011_, v_sz_3012_, v___x_3013_, v_b_3005_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_a_3015_; size_t v___x_3016_; size_t v___x_3017_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_a_3015_);
lean_dec_ref(v___x_3014_);
v___x_3016_ = ((size_t)1ULL);
v___x_3017_ = lean_usize_add(v_i_3004_, v___x_3016_);
v_i_3004_ = v___x_3017_;
v_b_3005_ = v_a_3015_;
goto _start;
}
else
{
return v___x_3014_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2___boxed(lean_object* v_as_3019_, lean_object* v_sz_3020_, lean_object* v_i_3021_, lean_object* v_b_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
size_t v_sz_boxed_3026_; size_t v_i_boxed_3027_; lean_object* v_res_3028_; 
v_sz_boxed_3026_ = lean_unbox_usize(v_sz_3020_);
lean_dec(v_sz_3020_);
v_i_boxed_3027_ = lean_unbox_usize(v_i_3021_);
lean_dec(v_i_3021_);
v_res_3028_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v_as_3019_, v_sz_boxed_3026_, v_i_boxed_3027_, v_b_3022_, v___y_3023_, v___y_3024_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec_ref(v_as_3019_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(lean_object* v_as_3029_, size_t v_i_3030_, size_t v_stop_3031_, lean_object* v_b_3032_){
_start:
{
uint8_t v___x_3033_; 
v___x_3033_ = lean_usize_dec_eq(v_i_3030_, v_stop_3031_);
if (v___x_3033_ == 0)
{
lean_object* v___x_3034_; lean_object* v_fst_3035_; lean_object* v_snd_3036_; lean_object* v___x_3037_; size_t v___x_3038_; size_t v___x_3039_; 
v___x_3034_ = lean_array_uget_borrowed(v_as_3029_, v_i_3030_);
v_fst_3035_ = lean_ctor_get(v___x_3034_, 0);
v_snd_3036_ = lean_ctor_get(v___x_3034_, 1);
lean_inc(v_snd_3036_);
lean_inc(v_fst_3035_);
v___x_3037_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3035_, v_snd_3036_, v_b_3032_);
v___x_3038_ = ((size_t)1ULL);
v___x_3039_ = lean_usize_add(v_i_3030_, v___x_3038_);
v_i_3030_ = v___x_3039_;
v_b_3032_ = v___x_3037_;
goto _start;
}
else
{
return v_b_3032_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3___boxed(lean_object* v_as_3041_, lean_object* v_i_3042_, lean_object* v_stop_3043_, lean_object* v_b_3044_){
_start:
{
size_t v_i_boxed_3045_; size_t v_stop_boxed_3046_; lean_object* v_res_3047_; 
v_i_boxed_3045_ = lean_unbox_usize(v_i_3042_);
lean_dec(v_i_3042_);
v_stop_boxed_3046_ = lean_unbox_usize(v_stop_3043_);
lean_dec(v_stop_3043_);
v_res_3047_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v_as_3041_, v_i_boxed_3045_, v_stop_boxed_3046_, v_b_3044_);
lean_dec_ref(v_as_3041_);
return v_res_3047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(lean_object* v_as_3048_, size_t v_i_3049_, size_t v_stop_3050_, lean_object* v_b_3051_){
_start:
{
lean_object* v___y_3053_; uint8_t v___x_3057_; 
v___x_3057_ = lean_usize_dec_eq(v_i_3049_, v_stop_3050_);
if (v___x_3057_ == 0)
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; uint8_t v___x_3061_; 
v___x_3058_ = lean_array_uget_borrowed(v_as_3048_, v_i_3049_);
v___x_3059_ = lean_unsigned_to_nat(0u);
v___x_3060_ = lean_array_get_size(v___x_3058_);
v___x_3061_ = lean_nat_dec_lt(v___x_3059_, v___x_3060_);
if (v___x_3061_ == 0)
{
v___y_3053_ = v_b_3051_;
goto v___jp_3052_;
}
else
{
uint8_t v___x_3062_; 
v___x_3062_ = lean_nat_dec_le(v___x_3060_, v___x_3060_);
if (v___x_3062_ == 0)
{
if (v___x_3061_ == 0)
{
v___y_3053_ = v_b_3051_;
goto v___jp_3052_;
}
else
{
size_t v___x_3063_; size_t v___x_3064_; lean_object* v___x_3065_; 
v___x_3063_ = ((size_t)0ULL);
v___x_3064_ = lean_usize_of_nat(v___x_3060_);
v___x_3065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_3058_, v___x_3063_, v___x_3064_, v_b_3051_);
v___y_3053_ = v___x_3065_;
goto v___jp_3052_;
}
}
else
{
size_t v___x_3066_; size_t v___x_3067_; lean_object* v___x_3068_; 
v___x_3066_ = ((size_t)0ULL);
v___x_3067_ = lean_usize_of_nat(v___x_3060_);
v___x_3068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__3(v___x_3058_, v___x_3066_, v___x_3067_, v_b_3051_);
v___y_3053_ = v___x_3068_;
goto v___jp_3052_;
}
}
}
else
{
return v_b_3051_;
}
v___jp_3052_:
{
size_t v___x_3054_; size_t v___x_3055_; 
v___x_3054_ = ((size_t)1ULL);
v___x_3055_ = lean_usize_add(v_i_3049_, v___x_3054_);
v_i_3049_ = v___x_3055_;
v_b_3051_ = v___y_3053_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5___boxed(lean_object* v_as_3069_, lean_object* v_i_3070_, lean_object* v_stop_3071_, lean_object* v_b_3072_){
_start:
{
size_t v_i_boxed_3073_; size_t v_stop_boxed_3074_; lean_object* v_res_3075_; 
v_i_boxed_3073_ = lean_unbox_usize(v_i_3070_);
lean_dec(v_i_3070_);
v_stop_boxed_3074_ = lean_unbox_usize(v_stop_3071_);
lean_dec(v_stop_3071_);
v_res_3075_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v_as_3069_, v_i_boxed_3073_, v_stop_boxed_3074_, v_b_3072_);
lean_dec_ref(v_as_3069_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(lean_object* v___y_3076_){
_start:
{
lean_object* v___x_3078_; lean_object* v_env_3079_; lean_object* v___x_3080_; lean_object* v_ext_3081_; lean_object* v_toEnvExtension_3082_; lean_object* v_asyncMode_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v_categories_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3078_ = lean_st_ref_get(v___y_3076_);
v_env_3079_ = lean_ctor_get(v___x_3078_, 0);
lean_inc_ref_n(v_env_3079_, 2);
lean_dec(v___x_3078_);
v___x_3080_ = l_Lean_Parser_parserExtension;
v_ext_3081_ = lean_ctor_get(v___x_3080_, 1);
v_toEnvExtension_3082_ = lean_ctor_get(v_ext_3081_, 0);
v_asyncMode_3083_ = lean_ctor_get(v_toEnvExtension_3082_, 2);
v___x_3084_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3085_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3084_, v___x_3080_, v_env_3079_, v_asyncMode_3083_);
v_categories_3086_ = lean_ctor_get(v___x_3085_, 2);
lean_inc_ref(v_categories_3086_);
lean_dec(v___x_3085_);
v___x_3087_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_3088_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_3086_, v___x_3087_);
lean_dec_ref(v_categories_3086_);
if (lean_obj_tag(v___x_3088_) == 1)
{
lean_object* v_val_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3126_; 
v_val_3089_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3091_ = v___x_3088_;
v_isShared_3092_ = v_isSharedCheck_3126_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_val_3089_);
lean_dec(v___x_3088_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3126_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___y_3094_; lean_object* v___x_3103_; lean_object* v_toEnvExtension_3104_; lean_object* v_exportEntriesFn_3105_; lean_object* v_asyncMode_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v_importedEntries_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v_exported_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; uint8_t v___x_3118_; 
v___x_3103_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3104_ = lean_ctor_get(v___x_3103_, 0);
v_exportEntriesFn_3105_ = lean_ctor_get(v___x_3103_, 4);
v_asyncMode_3106_ = lean_ctor_get(v_toEnvExtension_3104_, 2);
v___x_3107_ = lean_box(1);
v___x_3108_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_3109_ = lean_box(0);
lean_inc_ref_n(v_env_3079_, 2);
v___x_3110_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3108_, v_toEnvExtension_3104_, v_env_3079_, v_asyncMode_3106_, v___x_3109_);
v_importedEntries_3111_ = lean_ctor_get(v___x_3110_, 0);
lean_inc_ref(v_importedEntries_3111_);
lean_dec(v___x_3110_);
v___x_3112_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3107_, v___x_3103_, v_env_3079_, v_asyncMode_3106_, v___x_3109_);
lean_inc_ref(v_exportEntriesFn_3105_);
v___x_3113_ = lean_apply_2(v_exportEntriesFn_3105_, v_env_3079_, v___x_3112_);
v_exported_3114_ = lean_ctor_get(v___x_3113_, 0);
lean_inc(v_exported_3114_);
lean_dec_ref(v___x_3113_);
v___x_3115_ = lean_array_push(v_importedEntries_3111_, v_exported_3114_);
v___x_3116_ = lean_unsigned_to_nat(0u);
v___x_3117_ = lean_array_get_size(v___x_3115_);
v___x_3118_ = lean_nat_dec_lt(v___x_3116_, v___x_3117_);
if (v___x_3118_ == 0)
{
lean_dec_ref(v___x_3115_);
v___y_3094_ = v___x_3107_;
goto v___jp_3093_;
}
else
{
uint8_t v___x_3119_; 
v___x_3119_ = lean_nat_dec_le(v___x_3117_, v___x_3117_);
if (v___x_3119_ == 0)
{
if (v___x_3118_ == 0)
{
lean_dec_ref(v___x_3115_);
v___y_3094_ = v___x_3107_;
goto v___jp_3093_;
}
else
{
size_t v___x_3120_; size_t v___x_3121_; lean_object* v___x_3122_; 
v___x_3120_ = ((size_t)0ULL);
v___x_3121_ = lean_usize_of_nat(v___x_3117_);
v___x_3122_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3115_, v___x_3120_, v___x_3121_, v___x_3107_);
lean_dec_ref(v___x_3115_);
v___y_3094_ = v___x_3122_;
goto v___jp_3093_;
}
}
else
{
size_t v___x_3123_; size_t v___x_3124_; lean_object* v___x_3125_; 
v___x_3123_ = ((size_t)0ULL);
v___x_3124_ = lean_usize_of_nat(v___x_3117_);
v___x_3125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3115_, v___x_3123_, v___x_3124_, v___x_3107_);
lean_dec_ref(v___x_3115_);
v___y_3094_ = v___x_3125_;
goto v___jp_3093_;
}
}
v___jp_3093_:
{
lean_object* v_tables_3095_; lean_object* v_leadingTable_3096_; lean_object* v_trailingTable_3097_; lean_object* v_firstTokens_3098_; lean_object* v_firstTokens_3099_; lean_object* v___x_3101_; 
v_tables_3095_ = lean_ctor_get(v_val_3089_, 2);
v_leadingTable_3096_ = lean_ctor_get(v_tables_3095_, 0);
v_trailingTable_3097_ = lean_ctor_get(v_tables_3095_, 2);
lean_inc(v_trailingTable_3097_);
lean_inc(v_leadingTable_3096_);
lean_inc(v_val_3089_);
v_firstTokens_3098_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_3089_, v_leadingTable_3096_, v___y_3094_);
v_firstTokens_3099_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_3089_, v_trailingTable_3097_, v_firstTokens_3098_);
if (v_isShared_3092_ == 0)
{
lean_ctor_set_tag(v___x_3091_, 0);
lean_ctor_set(v___x_3091_, 0, v_firstTokens_3099_);
v___x_3101_ = v___x_3091_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_firstTokens_3099_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
else
{
lean_object* v___x_3127_; lean_object* v___x_3128_; 
lean_dec(v___x_3088_);
lean_dec_ref(v_env_3079_);
v___x_3127_ = lean_box(1);
v___x_3128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3127_);
return v___x_3128_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg___boxed(lean_object* v___y_3129_, lean_object* v___y_3130_){
_start:
{
lean_object* v_res_3131_; 
v_res_3131_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_3129_);
lean_dec(v___y_3129_);
return v_res_3131_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0(void){
_start:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3132_ = lean_box(1);
v___x_3133_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_3132_);
return v___x_3133_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2(void){
_start:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; 
v___x_3135_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__1));
v___x_3136_ = l_Lean_stringToMessageData(v___x_3135_);
return v___x_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(lean_object* v_a_3137_, lean_object* v_a_3138_){
_start:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v_env_3143_; lean_object* v_env_3144_; lean_object* v_env_3145_; lean_object* v___x_3146_; lean_object* v_toEnvExtension_3147_; lean_object* v_exportEntriesFn_3148_; lean_object* v_asyncMode_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v_importedEntries_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3206_; 
v___x_3140_ = lean_st_ref_get(v_a_3138_);
v___x_3141_ = lean_st_ref_get(v_a_3138_);
v___x_3142_ = lean_st_ref_get(v_a_3138_);
v_env_3143_ = lean_ctor_get(v___x_3140_, 0);
lean_inc_ref(v_env_3143_);
lean_dec(v___x_3140_);
v_env_3144_ = lean_ctor_get(v___x_3141_, 0);
lean_inc_ref(v_env_3144_);
lean_dec(v___x_3141_);
v_env_3145_ = lean_ctor_get(v___x_3142_, 0);
lean_inc_ref(v_env_3145_);
lean_dec(v___x_3142_);
v___x_3146_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_3147_ = lean_ctor_get(v___x_3146_, 0);
v_exportEntriesFn_3148_ = lean_ctor_get(v___x_3146_, 4);
v_asyncMode_3149_ = lean_ctor_get(v_toEnvExtension_3147_, 2);
v___x_3150_ = lean_box(1);
v___x_3151_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0);
v___x_3152_ = lean_box(0);
v___x_3153_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3151_, v_toEnvExtension_3147_, v_env_3143_, v_asyncMode_3149_, v___x_3152_);
v_importedEntries_3154_ = lean_ctor_get(v___x_3153_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3206_ == 0)
{
lean_object* v_unused_3207_; 
v_unused_3207_ = lean_ctor_get(v___x_3153_, 1);
lean_dec(v_unused_3207_);
v___x_3156_ = v___x_3153_;
v_isShared_3157_ = v_isSharedCheck_3206_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_importedEntries_3154_);
lean_dec(v___x_3153_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3206_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v_exported_3160_; lean_object* v___x_3161_; size_t v_sz_3162_; size_t v___x_3163_; lean_object* v___x_3164_; 
v___x_3158_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3150_, v___x_3146_, v_env_3145_, v_asyncMode_3149_, v___x_3152_);
lean_inc_ref(v_exportEntriesFn_3148_);
v___x_3159_ = lean_apply_2(v_exportEntriesFn_3148_, v_env_3144_, v___x_3158_);
v_exported_3160_ = lean_ctor_get(v___x_3159_, 0);
lean_inc(v_exported_3160_);
lean_dec_ref(v___x_3159_);
v___x_3161_ = lean_array_push(v_importedEntries_3154_, v_exported_3160_);
v_sz_3162_ = lean_array_size(v___x_3161_);
v___x_3163_ = ((size_t)0ULL);
v___x_3164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__2(v___x_3161_, v_sz_3162_, v___x_3163_, v___x_3150_, v_a_3137_, v_a_3138_);
lean_dec_ref(v___x_3161_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3165_; lean_object* v___x_3166_; lean_object* v_a_3167_; lean_object* v___x_3168_; 
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
lean_inc(v_a_3165_);
lean_dec_ref(v___x_3164_);
v___x_3166_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v_a_3138_);
v_a_3167_ = lean_ctor_get(v___x_3166_, 0);
lean_inc(v_a_3167_);
lean_dec_ref(v___x_3166_);
v___x_3168_ = l_Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10(v_a_3137_, v_a_3138_);
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_object* v_a_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; 
v_a_3169_ = lean_ctor_get(v___x_3168_, 0);
lean_inc(v_a_3169_);
lean_dec_ref(v___x_3168_);
v___x_3170_ = lean_box(0);
v___x_3171_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__11(v_a_3167_, v_a_3165_, v_a_3169_, v___x_3170_, v_a_3137_, v_a_3138_);
lean_dec(v_a_3165_);
lean_dec(v_a_3167_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_object* v_a_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3177_; 
v_a_3172_ = lean_ctor_get(v___x_3171_, 0);
lean_inc(v_a_3172_);
lean_dec_ref(v___x_3171_);
v___x_3173_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__2);
v___x_3174_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Doc_elabTacticExtension_spec__0_spec__1_spec__3___closed__0);
v___x_3175_ = l_Lean_MessageData_joinSep(v_a_3172_, v___x_3174_);
if (v_isShared_3157_ == 0)
{
lean_ctor_set_tag(v___x_3156_, 7);
lean_ctor_set(v___x_3156_, 1, v___x_3175_);
lean_ctor_set(v___x_3156_, 0, v___x_3174_);
v___x_3177_ = v___x_3156_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v___x_3174_);
lean_ctor_set(v_reuseFailAlloc_3181_, 1, v___x_3175_);
v___x_3177_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3178_ = l_Lean_MessageData_nestD(v___x_3177_);
v___x_3179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3173_);
lean_ctor_set(v___x_3179_, 1, v___x_3178_);
v___x_3180_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__12(v___x_3179_, v_a_3137_, v_a_3138_);
return v___x_3180_;
}
}
else
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3189_; 
lean_del_object(v___x_3156_);
v_a_3182_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3184_ = v___x_3171_;
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_3171_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3185_ == 0)
{
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3182_);
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
else
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
lean_dec(v_a_3167_);
lean_dec(v_a_3165_);
lean_del_object(v___x_3156_);
v_a_3190_ = lean_ctor_get(v___x_3168_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___x_3168_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3168_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3190_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
else
{
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3205_; 
lean_del_object(v___x_3156_);
v_a_3198_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3200_ = v___x_3164_;
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3164_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3203_; 
if (v_isShared_3201_ == 0)
{
v___x_3203_ = v___x_3200_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3198_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___boxed(lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_){
_start:
{
lean_object* v_res_3211_; 
v_res_3211_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_3208_, v_a_3209_);
lean_dec(v_a_3209_);
lean_dec_ref(v_a_3208_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags(lean_object* v___stx_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg(v_a_3213_, v_a_3214_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed(lean_object* v___stx_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_){
_start:
{
lean_object* v_res_3221_; 
v_res_3221_ = l_Lean_Elab_Tactic_Doc_elabPrintTacTags(v___stx_3217_, v_a_3218_, v_a_3219_);
lean_dec(v_a_3219_);
lean_dec_ref(v_a_3218_);
lean_dec(v___stx_3217_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(lean_object* v_00_u03b4_3222_, lean_object* v_t_3223_, lean_object* v_k_3224_, lean_object* v_fallback_3225_){
_start:
{
lean_object* v___x_3226_; 
v___x_3226_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_t_3223_, v_k_3224_, v_fallback_3225_);
return v___x_3226_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___boxed(lean_object* v_00_u03b4_3227_, lean_object* v_t_3228_, lean_object* v_k_3229_, lean_object* v_fallback_3230_){
_start:
{
lean_object* v_res_3231_; 
v_res_3231_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0(v_00_u03b4_3227_, v_t_3228_, v_k_3229_, v_fallback_3230_);
lean_dec(v_fallback_3230_);
lean_dec(v_k_3229_);
lean_dec(v_t_3228_);
return v_res_3231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(lean_object* v_as_3232_, size_t v_sz_3233_, size_t v_i_3234_, lean_object* v_b_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
lean_object* v___x_3239_; 
v___x_3239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___redArg(v_as_3232_, v_sz_3233_, v_i_3234_, v_b_3235_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1___boxed(lean_object* v_as_3240_, lean_object* v_sz_3241_, lean_object* v_i_3242_, lean_object* v_b_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_){
_start:
{
size_t v_sz_boxed_3247_; size_t v_i_boxed_3248_; lean_object* v_res_3249_; 
v_sz_boxed_3247_ = lean_unbox_usize(v_sz_3241_);
lean_dec(v_sz_3241_);
v_i_boxed_3248_ = lean_unbox_usize(v_i_3242_);
lean_dec(v_i_3242_);
v_res_3249_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__1(v_as_3240_, v_sz_boxed_3247_, v_i_boxed_3248_, v_b_3243_, v___y_3244_, v___y_3245_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec_ref(v_as_3240_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(lean_object* v___y_3250_, lean_object* v___y_3251_){
_start:
{
lean_object* v___x_3253_; 
v___x_3253_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___redArg(v___y_3251_);
return v___x_3253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3___boxed(lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_){
_start:
{
lean_object* v_res_3257_; 
v_res_3257_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3(v___y_3254_, v___y_3255_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(lean_object* v_val_3258_, lean_object* v___x_3259_, lean_object* v___x_3260_, lean_object* v_inst_3261_, lean_object* v_R_3262_, lean_object* v_a_3263_, lean_object* v_b_3264_){
_start:
{
lean_object* v___x_3265_; 
v___x_3265_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___redArg(v_val_3258_, v___x_3259_, v___x_3260_, v_a_3263_, v_b_3264_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5___boxed(lean_object* v_val_3266_, lean_object* v___x_3267_, lean_object* v___x_3268_, lean_object* v_inst_3269_, lean_object* v_R_3270_, lean_object* v_a_3271_, lean_object* v_b_3272_){
_start:
{
lean_object* v_res_3273_; 
v_res_3273_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__5(v_val_3266_, v___x_3267_, v___x_3268_, v_inst_3269_, v_R_3270_, v_a_3271_, v_b_3272_);
lean_dec_ref(v___x_3267_);
lean_dec_ref(v_val_3266_);
return v_res_3273_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8(lean_object* v_init_3274_, lean_object* v_t_3275_){
_start:
{
lean_object* v___x_3276_; 
v___x_3276_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__8_spec__17(v_init_3274_, v_t_3275_);
return v___x_3276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(lean_object* v_n_3277_, lean_object* v_as_3278_, lean_object* v_lo_3279_, lean_object* v_hi_3280_, lean_object* v_w_3281_, lean_object* v_hlo_3282_, lean_object* v_hhi_3283_){
_start:
{
lean_object* v___x_3284_; 
v___x_3284_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___redArg(v_n_3277_, v_as_3278_, v_lo_3279_, v_hi_3280_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9___boxed(lean_object* v_n_3285_, lean_object* v_as_3286_, lean_object* v_lo_3287_, lean_object* v_hi_3288_, lean_object* v_w_3289_, lean_object* v_hlo_3290_, lean_object* v_hhi_3291_){
_start:
{
lean_object* v_res_3292_; 
v_res_3292_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9(v_n_3285_, v_as_3286_, v_lo_3287_, v_hi_3288_, v_w_3289_, v_hlo_3290_, v_hhi_3291_);
lean_dec(v_hi_3288_);
lean_dec(v_n_3285_);
return v_res_3292_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(lean_object* v_00_u03b2_3293_, lean_object* v_x_3294_, lean_object* v_x_3295_){
_start:
{
lean_object* v___x_3296_; 
v___x_3296_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_x_3294_, v_x_3295_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3297_, lean_object* v_x_3298_, lean_object* v_x_3299_){
_start:
{
lean_object* v_res_3300_; 
v_res_3300_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4(v_00_u03b2_3297_, v_x_3298_, v_x_3299_);
lean_dec(v_x_3299_);
lean_dec_ref(v_x_3298_);
return v_res_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(lean_object* v_tac_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
lean_object* v___x_3305_; 
v___x_3305_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___redArg(v_tac_3301_, v___y_3303_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9___boxed(lean_object* v_tac_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l_Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9(v_tac_3306_, v___y_3307_, v___y_3308_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10(lean_object* v_00_u03b2_3311_, lean_object* v_k_3312_, lean_object* v_v_3313_, lean_object* v_t_3314_, lean_object* v_hl_3315_){
_start:
{
lean_object* v___x_3316_; 
v___x_3316_ = l_Std_DTreeMap_Internal_Impl_insert___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__10___redArg(v_k_3312_, v_v_3313_, v_t_3314_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(lean_object* v_as_3317_, lean_object* v_as_x27_3318_, lean_object* v_b_3319_, lean_object* v_a_3320_){
_start:
{
lean_object* v___x_3321_; 
v___x_3321_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___redArg(v_as_x27_3318_, v_b_3319_);
return v___x_3321_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11___boxed(lean_object* v_as_3322_, lean_object* v_as_x27_3323_, lean_object* v_b_3324_, lean_object* v_a_3325_){
_start:
{
lean_object* v_res_3326_; 
v_res_3326_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__11(v_as_3322_, v_as_x27_3323_, v_b_3324_, v_a_3325_);
lean_dec(v_as_x27_3323_);
lean_dec(v_as_3322_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(lean_object* v_00_u03b4_3327_, lean_object* v_t_3328_, lean_object* v_k_3329_){
_start:
{
lean_object* v___x_3330_; 
v___x_3330_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg(v_t_3328_, v_k_3329_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___boxed(lean_object* v_00_u03b4_3331_, lean_object* v_t_3332_, lean_object* v_k_3333_){
_start:
{
lean_object* v_res_3334_; 
v_res_3334_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12(v_00_u03b4_3331_, v_t_3332_, v_k_3333_);
lean_dec(v_k_3333_);
lean_dec(v_t_3332_);
return v_res_3334_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13(lean_object* v_00_u03b2_3335_, lean_object* v_x_3336_, lean_object* v_x_3337_){
_start:
{
lean_object* v___x_3338_; 
v___x_3338_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___redArg(v_x_3336_, v_x_3337_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13___boxed(lean_object* v_00_u03b2_3339_, lean_object* v_x_3340_, lean_object* v_x_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13(v_00_u03b2_3339_, v_x_3340_, v_x_3341_);
lean_dec(v_x_3341_);
lean_dec_ref(v_x_3340_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__19(lean_object* v_n_3343_, lean_object* v_lo_3344_, lean_object* v_hi_3345_, lean_object* v_hhi_3346_, lean_object* v_pivot_3347_, lean_object* v_as_3348_, lean_object* v_i_3349_, lean_object* v_k_3350_, lean_object* v_ilo_3351_, lean_object* v_ik_3352_, lean_object* v_w_3353_){
_start:
{
lean_object* v___x_3354_; 
v___x_3354_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__19___redArg(v_hi_3345_, v_pivot_3347_, v_as_3348_, v_i_3349_, v_k_3350_);
return v___x_3354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__19___boxed(lean_object* v_n_3355_, lean_object* v_lo_3356_, lean_object* v_hi_3357_, lean_object* v_hhi_3358_, lean_object* v_pivot_3359_, lean_object* v_as_3360_, lean_object* v_i_3361_, lean_object* v_k_3362_, lean_object* v_ilo_3363_, lean_object* v_ik_3364_, lean_object* v_w_3365_){
_start:
{
lean_object* v_res_3366_; 
v_res_3366_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__9_spec__19(v_n_3355_, v_lo_3356_, v_hi_3357_, v_hhi_3358_, v_pivot_3359_, v_as_3360_, v_i_3361_, v_k_3362_, v_ilo_3363_, v_ik_3364_, v_w_3365_);
lean_dec(v_hi_3357_);
lean_dec(v_lo_3356_);
lean_dec(v_n_3355_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(lean_object* v_as_3367_, size_t v_sz_3368_, size_t v_i_3369_, lean_object* v_b_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
lean_object* v___x_3374_; 
v___x_3374_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___redArg(v_as_3367_, v_sz_3368_, v_i_3369_, v_b_3370_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21___boxed(lean_object* v_as_3375_, lean_object* v_sz_3376_, lean_object* v_i_3377_, lean_object* v_b_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
size_t v_sz_boxed_3382_; size_t v_i_boxed_3383_; lean_object* v_res_3384_; 
v_sz_boxed_3382_ = lean_unbox_usize(v_sz_3376_);
lean_dec(v_sz_3376_);
v_i_boxed_3383_ = lean_unbox_usize(v_i_3377_);
lean_dec(v_i_3377_);
v_res_3384_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__21(v_as_3375_, v_sz_boxed_3382_, v_i_boxed_3383_, v_b_3378_, v___y_3379_, v___y_3380_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
lean_dec_ref(v_as_3375_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(lean_object* v_init_3385_, lean_object* v_t_3386_){
_start:
{
lean_object* v___x_3387_; 
v___x_3387_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23_spec__27(v_init_3385_, v_t_3386_);
return v___x_3387_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23___boxed(lean_object* v_init_3388_, lean_object* v_t_3389_){
_start:
{
lean_object* v_res_3390_; 
v_res_3390_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__23(v_init_3388_, v_t_3389_);
lean_dec(v_t_3389_);
return v_res_3390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24(lean_object* v_n_3391_, lean_object* v_as_3392_, lean_object* v_lo_3393_, lean_object* v_hi_3394_, lean_object* v_w_3395_, lean_object* v_hlo_3396_, lean_object* v_hhi_3397_){
_start:
{
lean_object* v___x_3398_; 
v___x_3398_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___redArg(v_n_3391_, v_as_3392_, v_lo_3393_, v_hi_3394_);
return v___x_3398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24___boxed(lean_object* v_n_3399_, lean_object* v_as_3400_, lean_object* v_lo_3401_, lean_object* v_hi_3402_, lean_object* v_w_3403_, lean_object* v_hlo_3404_, lean_object* v_hhi_3405_){
_start:
{
lean_object* v_res_3406_; 
v_res_3406_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24(v_n_3399_, v_as_3400_, v_lo_3401_, v_hi_3402_, v_w_3403_, v_hlo_3404_, v_hhi_3405_);
lean_dec(v_hi_3402_);
lean_dec(v_n_3399_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__25(lean_object* v_init_3407_, lean_object* v_x_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_){
_start:
{
lean_object* v___x_3412_; 
v___x_3412_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__25___redArg(v_init_3407_, v_x_3408_);
return v___x_3412_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__25___boxed(lean_object* v_init_3413_, lean_object* v_x_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
lean_object* v_res_3418_; 
v_res_3418_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__25(v_init_3413_, v_x_3414_, v___y_3415_, v___y_3416_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(lean_object* v_00_u03b2_3419_, lean_object* v_x_3420_, size_t v_x_3421_, lean_object* v_x_3422_){
_start:
{
lean_object* v___x_3423_; 
v___x_3423_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___redArg(v_x_3420_, v_x_3421_, v_x_3422_);
return v___x_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b2_3424_, lean_object* v_x_3425_, lean_object* v_x_3426_, lean_object* v_x_3427_){
_start:
{
size_t v_x_20997__boxed_3428_; lean_object* v_res_3429_; 
v_x_20997__boxed_3428_ = lean_unbox_usize(v_x_3426_);
lean_dec(v_x_3426_);
v_res_3429_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6(v_00_u03b2_3424_, v_x_3425_, v_x_20997__boxed_3428_, v_x_3427_);
lean_dec(v_x_3427_);
lean_dec_ref(v_x_3425_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(lean_object* v_as_3430_, lean_object* v_k_3431_, lean_object* v_x_3432_, lean_object* v_x_3433_, lean_object* v_x_3434_){
_start:
{
lean_object* v___x_3435_; 
v___x_3435_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___redArg(v_as_3430_, v_k_3431_, v_x_3432_, v_x_3433_);
return v___x_3435_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11___boxed(lean_object* v_as_3436_, lean_object* v_k_3437_, lean_object* v_x_3438_, lean_object* v_x_3439_, lean_object* v_x_3440_){
_start:
{
lean_object* v_res_3441_; 
v_res_3441_ = l_Array_binSearchAux___at___00Lean_Parser_Tactic_Doc_customTacticName___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__9_spec__11(v_as_3436_, v_k_3437_, v_x_3438_, v_x_3439_, v_x_3440_);
lean_dec_ref(v_k_3437_);
lean_dec_ref(v_as_3436_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16(lean_object* v_00_u03b2_3442_, lean_object* v_m_3443_, lean_object* v_a_3444_){
_start:
{
lean_object* v___x_3445_; 
v___x_3445_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___redArg(v_m_3443_, v_a_3444_);
return v___x_3445_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16___boxed(lean_object* v_00_u03b2_3446_, lean_object* v_m_3447_, lean_object* v_a_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16(v_00_u03b2_3446_, v_m_3447_, v_a_3448_);
lean_dec(v_a_3448_);
lean_dec_ref(v_m_3447_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24_spec__29(lean_object* v_n_3450_, lean_object* v_lo_3451_, lean_object* v_hi_3452_, lean_object* v_hhi_3453_, lean_object* v_pivot_3454_, lean_object* v_as_3455_, lean_object* v_i_3456_, lean_object* v_k_3457_, lean_object* v_ilo_3458_, lean_object* v_ik_3459_, lean_object* v_w_3460_){
_start:
{
lean_object* v___x_3461_; 
v___x_3461_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24_spec__29___redArg(v_hi_3452_, v_pivot_3454_, v_as_3455_, v_i_3456_, v_k_3457_);
return v___x_3461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24_spec__29___boxed(lean_object* v_n_3462_, lean_object* v_lo_3463_, lean_object* v_hi_3464_, lean_object* v_hhi_3465_, lean_object* v_pivot_3466_, lean_object* v_as_3467_, lean_object* v_i_3468_, lean_object* v_k_3469_, lean_object* v_ilo_3470_, lean_object* v_ik_3471_, lean_object* v_w_3472_){
_start:
{
lean_object* v_res_3473_; 
v_res_3473_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Tactic_Doc_allTagsWithInfo___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__10_spec__24_spec__29(v_n_3462_, v_lo_3463_, v_hi_3464_, v_hhi_3465_, v_pivot_3466_, v_as_3467_, v_i_3468_, v_k_3469_, v_ilo_3470_, v_ik_3471_, v_w_3472_);
lean_dec(v_hi_3464_);
lean_dec(v_lo_3463_);
lean_dec(v_n_3462_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(lean_object* v_00_u03b2_3474_, lean_object* v_keys_3475_, lean_object* v_vals_3476_, lean_object* v_heq_3477_, lean_object* v_i_3478_, lean_object* v_k_3479_){
_start:
{
lean_object* v___x_3480_; 
v___x_3480_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___redArg(v_keys_3475_, v_vals_3476_, v_i_3478_, v_k_3479_);
return v___x_3480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15___boxed(lean_object* v_00_u03b2_3481_, lean_object* v_keys_3482_, lean_object* v_vals_3483_, lean_object* v_heq_3484_, lean_object* v_i_3485_, lean_object* v_k_3486_){
_start:
{
lean_object* v_res_3487_; 
v_res_3487_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4_spec__6_spec__15(v_00_u03b2_3481_, v_keys_3482_, v_vals_3483_, v_heq_3484_, v_i_3485_, v_k_3486_);
lean_dec(v_k_3486_);
lean_dec_ref(v_vals_3483_);
lean_dec_ref(v_keys_3482_);
return v_res_3487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24(lean_object* v_00_u03b2_3488_, lean_object* v_a_3489_, lean_object* v_x_3490_){
_start:
{
lean_object* v___x_3491_; 
v___x_3491_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___redArg(v_a_3489_, v_x_3490_);
return v___x_3491_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24___boxed(lean_object* v_00_u03b2_3492_, lean_object* v_a_3493_, lean_object* v_x_3494_){
_start:
{
lean_object* v_res_3495_; 
v_res_3495_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f_x27___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__13_spec__16_spec__24(v_00_u03b2_3492_, v_a_3493_, v_x_3494_);
lean_dec(v_x_3494_);
lean_dec(v_a_3493_);
return v_res_3495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1(){
_start:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3510_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3511_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__1));
v___x_3512_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3513_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_elabPrintTacTags___boxed), 4, 0);
v___x_3514_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3510_, v___x_3511_, v___x_3512_, v___x_3513_);
return v___x_3514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___boxed(lean_object* v_a_3515_){
_start:
{
lean_object* v_res_3516_; 
v_res_3516_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1();
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3(){
_start:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3519_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3520_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___closed__0));
v___x_3521_ = l_Lean_addBuiltinDocString(v___x_3519_, v___x_3520_);
return v___x_3521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3___boxed(lean_object* v_a_3522_){
_start:
{
lean_object* v_res_3523_; 
v_res_3523_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_docString__3();
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5(){
_start:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3550_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags__1___closed__3));
v___x_3551_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___closed__6));
v___x_3552_ = l_Lean_addBuiltinDeclarationRanges(v___x_3550_, v___x_3551_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5___boxed(lean_object* v_a_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_elabPrintTacTags___regBuiltin_Lean_Elab_Tactic_Doc_elabPrintTacTags_declRange__5();
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(lean_object* v_env_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, uint8_t v_includeUnnamed_3558_, lean_object* v_x_3559_, lean_object* v_____s_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_){
_start:
{
lean_object* v_fst_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3619_; 
v_fst_3566_ = lean_ctor_get(v_x_3559_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v_x_3559_);
if (v_isSharedCheck_3619_ == 0)
{
lean_object* v_unused_3620_; 
v_unused_3620_ = lean_ctor_get(v_x_3559_, 1);
lean_dec(v_unused_3620_);
v___x_3568_ = v_x_3559_;
v_isShared_3569_ = v_isSharedCheck_3619_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_fst_3566_);
lean_dec(v_x_3559_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3619_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
lean_object* v_userName_3571_; lean_object* v___y_3572_; lean_object* v___x_3604_; 
lean_inc(v_fst_3566_);
lean_inc_ref(v_env_3555_);
v___x_3604_ = l_Lean_Parser_Tactic_Doc_alternativeOfTactic(v_env_3555_, v_fst_3566_);
if (lean_obj_tag(v___x_3604_) == 1)
{
lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3612_; 
lean_del_object(v___x_3568_);
lean_dec(v_fst_3566_);
lean_dec_ref(v_env_3555_);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3612_ == 0)
{
lean_object* v_unused_3613_; 
v_unused_3613_ = lean_ctor_get(v___x_3604_, 0);
lean_dec(v_unused_3613_);
v___x_3606_ = v___x_3604_;
v_isShared_3607_ = v_isSharedCheck_3612_;
goto v_resetjp_3605_;
}
else
{
lean_dec(v___x_3604_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3612_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3609_; 
if (v_isShared_3607_ == 0)
{
lean_ctor_set(v___x_3606_, 0, v_____s_3560_);
v___x_3609_ = v___x_3606_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_____s_3560_);
v___x_3609_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
lean_object* v___x_3610_; 
v___x_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3609_);
return v___x_3610_;
}
}
}
else
{
lean_object* v___x_3614_; 
lean_dec(v___x_3604_);
v___x_3614_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_showParserName___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__6_spec__12___redArg(v_a_3557_, v_fst_3566_);
if (lean_obj_tag(v___x_3614_) == 1)
{
lean_object* v_val_3615_; 
v_val_3615_ = lean_ctor_get(v___x_3614_, 0);
lean_inc(v_val_3615_);
lean_dec_ref(v___x_3614_);
v_userName_3571_ = v_val_3615_;
v___y_3572_ = v___y_3563_;
goto v___jp_3570_;
}
else
{
lean_dec(v___x_3614_);
if (v_includeUnnamed_3558_ == 0)
{
lean_object* v___x_3616_; lean_object* v___x_3617_; 
lean_del_object(v___x_3568_);
lean_dec(v_fst_3566_);
lean_dec_ref(v_env_3555_);
v___x_3616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3616_, 0, v_____s_3560_);
v___x_3617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3616_);
return v___x_3617_;
}
else
{
lean_object* v___x_3618_; 
lean_inc(v_fst_3566_);
v___x_3618_ = l_Lean_Name_toString(v_fst_3566_, v_includeUnnamed_3558_);
v_userName_3571_ = v___x_3618_;
v___y_3572_ = v___y_3563_;
goto v___jp_3570_;
}
}
}
v___jp_3570_:
{
uint8_t v___x_3573_; lean_object* v___x_3574_; 
v___x_3573_ = 1;
lean_inc(v_fst_3566_);
lean_inc_ref(v_env_3555_);
v___x_3574_ = l_Lean_findDocString_x3f(v_env_3555_, v_fst_3566_, v___x_3573_);
if (lean_obj_tag(v___x_3574_) == 0)
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3588_; 
lean_del_object(v___x_3568_);
v_a_3575_ = lean_ctor_get(v___x_3574_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3574_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3577_ = v___x_3574_;
v_isShared_3578_ = v_isSharedCheck_3588_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___x_3574_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3588_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3586_; 
v___x_3579_ = l_Lean_NameSet_empty;
v___x_3580_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_a_3556_, v_fst_3566_, v___x_3579_);
lean_inc(v_fst_3566_);
v___x_3581_ = l_Lean_Parser_Tactic_Doc_getTacticExtensions(v_env_3555_, v_fst_3566_);
v___x_3582_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3582_, 0, v_fst_3566_);
lean_ctor_set(v___x_3582_, 1, v_userName_3571_);
lean_ctor_set(v___x_3582_, 2, v___x_3580_);
lean_ctor_set(v___x_3582_, 3, v_a_3575_);
lean_ctor_set(v___x_3582_, 4, v___x_3581_);
v___x_3583_ = lean_array_push(v_____s_3560_, v___x_3582_);
v___x_3584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3583_);
if (v_isShared_3578_ == 0)
{
lean_ctor_set(v___x_3577_, 0, v___x_3584_);
v___x_3586_ = v___x_3577_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v___x_3584_);
v___x_3586_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
return v___x_3586_;
}
}
}
else
{
lean_object* v_a_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3603_; 
lean_dec_ref(v_userName_3571_);
lean_dec(v_fst_3566_);
lean_dec_ref(v_____s_3560_);
lean_dec_ref(v_env_3555_);
v_a_3589_ = lean_ctor_get(v___x_3574_, 0);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3574_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3591_ = v___x_3574_;
v_isShared_3592_ = v_isSharedCheck_3603_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_a_3589_);
lean_dec(v___x_3574_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3603_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v_ref_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3598_; 
v_ref_3593_ = lean_ctor_get(v___y_3572_, 5);
v___x_3594_ = lean_io_error_to_string(v_a_3589_);
v___x_3595_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3595_, 0, v___x_3594_);
v___x_3596_ = l_Lean_MessageData_ofFormat(v___x_3595_);
lean_inc(v_ref_3593_);
if (v_isShared_3569_ == 0)
{
lean_ctor_set(v___x_3568_, 1, v___x_3596_);
lean_ctor_set(v___x_3568_, 0, v_ref_3593_);
v___x_3598_ = v___x_3568_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_ref_3593_);
lean_ctor_set(v_reuseFailAlloc_3602_, 1, v___x_3596_);
v___x_3598_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
lean_object* v___x_3600_; 
if (v_isShared_3592_ == 0)
{
lean_ctor_set(v___x_3591_, 0, v___x_3598_);
v___x_3600_ = v___x_3591_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v___x_3598_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed(lean_object* v_env_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_includeUnnamed_3624_, lean_object* v_x_3625_, lean_object* v_____s_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
uint8_t v_includeUnnamed_boxed_3632_; lean_object* v_res_3633_; 
v_includeUnnamed_boxed_3632_ = lean_unbox(v_includeUnnamed_3624_);
v_res_3633_ = l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0(v_env_3621_, v_a_3622_, v_a_3623_, v_includeUnnamed_boxed_3632_, v_x_3625_, v_____s_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec(v_a_3623_);
lean_dec(v_a_3622_);
return v_res_3633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(lean_object* v_as_3634_, size_t v_sz_3635_, size_t v_i_3636_, lean_object* v_b_3637_){
_start:
{
uint8_t v___x_3639_; 
v___x_3639_ = lean_usize_dec_lt(v_i_3636_, v_sz_3635_);
if (v___x_3639_ == 0)
{
lean_object* v___x_3640_; 
v___x_3640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3640_, 0, v_b_3637_);
return v___x_3640_;
}
else
{
lean_object* v_a_3641_; lean_object* v_fst_3642_; lean_object* v_snd_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; size_t v___x_3648_; size_t v___x_3649_; 
v_a_3641_ = lean_array_uget_borrowed(v_as_3634_, v_i_3636_);
v_fst_3642_ = lean_ctor_get(v_a_3641_, 0);
v_snd_3643_ = lean_ctor_get(v_a_3641_, 1);
v___x_3644_ = l_Lean_NameSet_empty;
v___x_3645_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__0___redArg(v_b_3637_, v_fst_3642_, v___x_3644_);
lean_inc(v_snd_3643_);
v___x_3646_ = l_Lean_NameSet_insert(v___x_3645_, v_snd_3643_);
lean_inc(v_fst_3642_);
v___x_3647_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3642_, v___x_3646_, v_b_3637_);
v___x_3648_ = ((size_t)1ULL);
v___x_3649_ = lean_usize_add(v_i_3636_, v___x_3648_);
v_i_3636_ = v___x_3649_;
v_b_3637_ = v___x_3647_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg___boxed(lean_object* v_as_3651_, lean_object* v_sz_3652_, lean_object* v_i_3653_, lean_object* v_b_3654_, lean_object* v___y_3655_){
_start:
{
size_t v_sz_boxed_3656_; size_t v_i_boxed_3657_; lean_object* v_res_3658_; 
v_sz_boxed_3656_ = lean_unbox_usize(v_sz_3652_);
lean_dec(v_sz_3652_);
v_i_boxed_3657_ = lean_unbox_usize(v_i_3653_);
lean_dec(v_i_3653_);
v_res_3658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_3651_, v_sz_boxed_3656_, v_i_boxed_3657_, v_b_3654_);
lean_dec_ref(v_as_3651_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(lean_object* v_as_3659_, size_t v_sz_3660_, size_t v_i_3661_, lean_object* v_b_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
uint8_t v___x_3668_; 
v___x_3668_ = lean_usize_dec_lt(v_i_3661_, v_sz_3660_);
if (v___x_3668_ == 0)
{
lean_object* v___x_3669_; 
v___x_3669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3669_, 0, v_b_3662_);
return v___x_3669_;
}
else
{
lean_object* v_a_3670_; size_t v_sz_3671_; size_t v___x_3672_; lean_object* v___x_3673_; 
v_a_3670_ = lean_array_uget_borrowed(v_as_3659_, v_i_3661_);
v_sz_3671_ = lean_array_size(v_a_3670_);
v___x_3672_ = ((size_t)0ULL);
v___x_3673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_a_3670_, v_sz_3671_, v___x_3672_, v_b_3662_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v_a_3674_; size_t v___x_3675_; size_t v___x_3676_; 
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
lean_inc(v_a_3674_);
lean_dec_ref(v___x_3673_);
v___x_3675_ = ((size_t)1ULL);
v___x_3676_ = lean_usize_add(v_i_3661_, v___x_3675_);
v_i_3661_ = v___x_3676_;
v_b_3662_ = v_a_3674_;
goto _start;
}
else
{
return v___x_3673_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1___boxed(lean_object* v_as_3678_, lean_object* v_sz_3679_, lean_object* v_i_3680_, lean_object* v_b_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_){
_start:
{
size_t v_sz_boxed_3687_; size_t v_i_boxed_3688_; lean_object* v_res_3689_; 
v_sz_boxed_3687_ = lean_unbox_usize(v_sz_3679_);
lean_dec(v_sz_3679_);
v_i_boxed_3688_ = lean_unbox_usize(v_i_3680_);
lean_dec(v_i_3680_);
v_res_3689_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v_as_3678_, v_sz_boxed_3687_, v_i_boxed_3688_, v_b_3681_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec_ref(v_as_3678_);
return v_res_3689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(lean_object* v_f_3690_, lean_object* v_keys_3691_, lean_object* v_vals_3692_, lean_object* v_i_3693_, lean_object* v_acc_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_){
_start:
{
lean_object* v___x_3700_; uint8_t v___x_3701_; 
v___x_3700_ = lean_array_get_size(v_keys_3691_);
v___x_3701_ = lean_nat_dec_lt(v_i_3693_, v___x_3700_);
if (v___x_3701_ == 0)
{
lean_object* v___x_3702_; lean_object* v___x_3703_; 
lean_dec(v_i_3693_);
lean_dec_ref(v_f_3690_);
v___x_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3702_, 0, v_acc_3694_);
v___x_3703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3702_);
return v___x_3703_;
}
else
{
lean_object* v_k_3704_; lean_object* v_v_3705_; lean_object* v___x_3706_; 
v_k_3704_ = lean_array_fget_borrowed(v_keys_3691_, v_i_3693_);
v_v_3705_ = lean_array_fget_borrowed(v_vals_3692_, v_i_3693_);
lean_inc_ref(v_f_3690_);
lean_inc(v___y_3698_);
lean_inc_ref(v___y_3697_);
lean_inc(v___y_3696_);
lean_inc_ref(v___y_3695_);
lean_inc(v_v_3705_);
lean_inc(v_k_3704_);
v___x_3706_ = lean_apply_8(v_f_3690_, v_acc_3694_, v_k_3704_, v_v_3705_, v___y_3695_, v___y_3696_, v___y_3697_, v___y_3698_, lean_box(0));
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v_a_3707_; 
v_a_3707_ = lean_ctor_get(v___x_3706_, 0);
lean_inc(v_a_3707_);
if (lean_obj_tag(v_a_3707_) == 0)
{
lean_dec_ref(v_a_3707_);
lean_dec(v_i_3693_);
lean_dec_ref(v_f_3690_);
return v___x_3706_;
}
else
{
lean_object* v_a_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
lean_dec_ref(v___x_3706_);
v_a_3708_ = lean_ctor_get(v_a_3707_, 0);
lean_inc(v_a_3708_);
lean_dec_ref(v_a_3707_);
v___x_3709_ = lean_unsigned_to_nat(1u);
v___x_3710_ = lean_nat_add(v_i_3693_, v___x_3709_);
lean_dec(v_i_3693_);
v_i_3693_ = v___x_3710_;
v_acc_3694_ = v_a_3708_;
goto _start;
}
}
else
{
lean_dec(v_i_3693_);
lean_dec_ref(v_f_3690_);
return v___x_3706_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_f_3712_, lean_object* v_keys_3713_, lean_object* v_vals_3714_, lean_object* v_i_3715_, lean_object* v_acc_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_){
_start:
{
lean_object* v_res_3722_; 
v_res_3722_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3712_, v_keys_3713_, v_vals_3714_, v_i_3715_, v_acc_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
lean_dec(v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec(v___y_3718_);
lean_dec_ref(v___y_3717_);
lean_dec_ref(v_vals_3714_);
lean_dec_ref(v_keys_3713_);
return v_res_3722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(lean_object* v_f_3723_, lean_object* v_x_3724_, lean_object* v_x_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_){
_start:
{
if (lean_obj_tag(v_x_3724_) == 0)
{
lean_object* v_es_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3753_; 
v_es_3731_ = lean_ctor_get(v_x_3724_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v_x_3724_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3733_ = v_x_3724_;
v_isShared_3734_ = v_isSharedCheck_3753_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_es_3731_);
lean_dec(v_x_3724_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3753_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3735_; lean_object* v___x_3736_; uint8_t v___x_3737_; 
v___x_3735_ = lean_unsigned_to_nat(0u);
v___x_3736_ = lean_array_get_size(v_es_3731_);
v___x_3737_ = lean_nat_dec_lt(v___x_3735_, v___x_3736_);
if (v___x_3737_ == 0)
{
lean_object* v___x_3739_; 
lean_dec_ref(v_es_3731_);
lean_dec_ref(v_f_3723_);
if (v_isShared_3734_ == 0)
{
lean_ctor_set_tag(v___x_3733_, 1);
lean_ctor_set(v___x_3733_, 0, v_x_3725_);
v___x_3739_ = v___x_3733_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_x_3725_);
v___x_3739_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
lean_object* v___x_3740_; 
v___x_3740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3739_);
return v___x_3740_;
}
}
else
{
uint8_t v___x_3742_; 
v___x_3742_ = lean_nat_dec_le(v___x_3736_, v___x_3736_);
if (v___x_3742_ == 0)
{
if (v___x_3737_ == 0)
{
lean_object* v___x_3744_; 
lean_dec_ref(v_es_3731_);
lean_dec_ref(v_f_3723_);
if (v_isShared_3734_ == 0)
{
lean_ctor_set_tag(v___x_3733_, 1);
lean_ctor_set(v___x_3733_, 0, v_x_3725_);
v___x_3744_ = v___x_3733_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_x_3725_);
v___x_3744_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
lean_object* v___x_3745_; 
v___x_3745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3744_);
return v___x_3745_;
}
}
else
{
size_t v___x_3747_; size_t v___x_3748_; lean_object* v___x_3749_; 
lean_del_object(v___x_3733_);
v___x_3747_ = ((size_t)0ULL);
v___x_3748_ = lean_usize_of_nat(v___x_3736_);
v___x_3749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3723_, v_es_3731_, v___x_3747_, v___x_3748_, v_x_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_);
lean_dec_ref(v_es_3731_);
return v___x_3749_;
}
}
else
{
size_t v___x_3750_; size_t v___x_3751_; lean_object* v___x_3752_; 
lean_del_object(v___x_3733_);
v___x_3750_ = ((size_t)0ULL);
v___x_3751_ = lean_usize_of_nat(v___x_3736_);
v___x_3752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3723_, v_es_3731_, v___x_3750_, v___x_3751_, v_x_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_);
lean_dec_ref(v_es_3731_);
return v___x_3752_;
}
}
}
}
else
{
lean_object* v_ks_3754_; lean_object* v_vs_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; 
v_ks_3754_ = lean_ctor_get(v_x_3724_, 0);
lean_inc_ref(v_ks_3754_);
v_vs_3755_ = lean_ctor_get(v_x_3724_, 1);
lean_inc_ref(v_vs_3755_);
lean_dec_ref(v_x_3724_);
v___x_3756_ = lean_unsigned_to_nat(0u);
v___x_3757_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_3723_, v_ks_3754_, v_vs_3755_, v___x_3756_, v_x_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_);
lean_dec_ref(v_vs_3755_);
lean_dec_ref(v_ks_3754_);
return v___x_3757_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(lean_object* v_f_3758_, lean_object* v_as_3759_, size_t v_i_3760_, size_t v_stop_3761_, lean_object* v_b_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_){
_start:
{
lean_object* v_a_3769_; lean_object* v___y_3774_; uint8_t v___x_3777_; 
v___x_3777_ = lean_usize_dec_eq(v_i_3760_, v_stop_3761_);
if (v___x_3777_ == 0)
{
lean_object* v___x_3778_; 
v___x_3778_ = lean_array_uget_borrowed(v_as_3759_, v_i_3760_);
switch(lean_obj_tag(v___x_3778_))
{
case 0:
{
lean_object* v_key_3779_; lean_object* v_val_3780_; lean_object* v___x_3781_; 
v_key_3779_ = lean_ctor_get(v___x_3778_, 0);
v_val_3780_ = lean_ctor_get(v___x_3778_, 1);
lean_inc_ref(v_f_3758_);
lean_inc(v___y_3766_);
lean_inc_ref(v___y_3765_);
lean_inc(v___y_3764_);
lean_inc_ref(v___y_3763_);
lean_inc(v_val_3780_);
lean_inc(v_key_3779_);
v___x_3781_ = lean_apply_8(v_f_3758_, v_b_3762_, v_key_3779_, v_val_3780_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_, lean_box(0));
v___y_3774_ = v___x_3781_;
goto v___jp_3773_;
}
case 1:
{
lean_object* v_node_3782_; lean_object* v___x_3783_; 
v_node_3782_ = lean_ctor_get(v___x_3778_, 0);
lean_inc(v_node_3782_);
lean_inc_ref(v_f_3758_);
v___x_3783_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3758_, v_node_3782_, v_b_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
v___y_3774_ = v___x_3783_;
goto v___jp_3773_;
}
default: 
{
v_a_3769_ = v_b_3762_;
goto v___jp_3768_;
}
}
}
else
{
lean_object* v___x_3784_; lean_object* v___x_3785_; 
lean_dec_ref(v_f_3758_);
v___x_3784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3784_, 0, v_b_3762_);
v___x_3785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3784_);
return v___x_3785_;
}
v___jp_3768_:
{
size_t v___x_3770_; size_t v___x_3771_; 
v___x_3770_ = ((size_t)1ULL);
v___x_3771_ = lean_usize_add(v_i_3760_, v___x_3770_);
v_i_3760_ = v___x_3771_;
v_b_3762_ = v_a_3769_;
goto _start;
}
v___jp_3773_:
{
if (lean_obj_tag(v___y_3774_) == 0)
{
lean_object* v_a_3775_; 
v_a_3775_ = lean_ctor_get(v___y_3774_, 0);
if (lean_obj_tag(v_a_3775_) == 0)
{
lean_dec_ref(v_f_3758_);
return v___y_3774_;
}
else
{
lean_object* v_a_3776_; 
lean_inc_ref(v_a_3775_);
lean_dec_ref(v___y_3774_);
v_a_3776_ = lean_ctor_get(v_a_3775_, 0);
lean_inc(v_a_3776_);
lean_dec_ref(v_a_3775_);
v_a_3769_ = v_a_3776_;
goto v___jp_3768_;
}
}
else
{
lean_dec_ref(v_f_3758_);
return v___y_3774_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_f_3786_, lean_object* v_as_3787_, lean_object* v_i_3788_, lean_object* v_stop_3789_, lean_object* v_b_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_){
_start:
{
size_t v_i_boxed_3796_; size_t v_stop_boxed_3797_; lean_object* v_res_3798_; 
v_i_boxed_3796_ = lean_unbox_usize(v_i_3788_);
lean_dec(v_i_3788_);
v_stop_boxed_3797_ = lean_unbox_usize(v_stop_3789_);
lean_dec(v_stop_3789_);
v_res_3798_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_3786_, v_as_3787_, v_i_boxed_3796_, v_stop_boxed_3797_, v_b_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec_ref(v_as_3787_);
return v_res_3798_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_f_3799_, lean_object* v_x_3800_, lean_object* v_x_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
lean_object* v_res_3807_; 
v_res_3807_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_3799_, v_x_3800_, v_x_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
return v_res_3807_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(lean_object* v_f_3808_, lean_object* v_s_3809_, lean_object* v_a_3810_, lean_object* v_b_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_){
_start:
{
lean_object* v___x_3817_; lean_object* v___x_3818_; 
v___x_3817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3817_, 0, v_a_3810_);
lean_ctor_set(v___x_3817_, 1, v_b_3811_);
lean_inc(v___y_3815_);
lean_inc_ref(v___y_3814_);
lean_inc(v___y_3813_);
lean_inc_ref(v___y_3812_);
v___x_3818_ = lean_apply_7(v_f_3808_, v___x_3817_, v_s_3809_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, lean_box(0));
if (lean_obj_tag(v___x_3818_) == 0)
{
lean_object* v_a_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3845_; 
v_a_3819_ = lean_ctor_get(v___x_3818_, 0);
v_isSharedCheck_3845_ = !lean_is_exclusive(v___x_3818_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3821_ = v___x_3818_;
v_isShared_3822_ = v_isSharedCheck_3845_;
goto v_resetjp_3820_;
}
else
{
lean_inc(v_a_3819_);
lean_dec(v___x_3818_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3845_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
if (lean_obj_tag(v_a_3819_) == 0)
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3833_; 
v_a_3823_ = lean_ctor_get(v_a_3819_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v_a_3819_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3825_ = v_a_3819_;
v_isShared_3826_ = v_isSharedCheck_3833_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v_a_3819_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3833_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3828_; 
if (v_isShared_3826_ == 0)
{
v___x_3828_ = v___x_3825_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3823_);
v___x_3828_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
lean_object* v___x_3830_; 
if (v_isShared_3822_ == 0)
{
lean_ctor_set(v___x_3821_, 0, v___x_3828_);
v___x_3830_ = v___x_3821_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3828_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
else
{
lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3844_; 
v_a_3834_ = lean_ctor_get(v_a_3819_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v_a_3819_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3836_ = v_a_3819_;
v_isShared_3837_ = v_isSharedCheck_3844_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v_a_3819_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3844_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3839_; 
if (v_isShared_3837_ == 0)
{
v___x_3839_ = v___x_3836_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_a_3834_);
v___x_3839_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
lean_object* v___x_3841_; 
if (v_isShared_3822_ == 0)
{
lean_ctor_set(v___x_3821_, 0, v___x_3839_);
v___x_3841_ = v___x_3821_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v___x_3839_);
v___x_3841_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
return v___x_3841_;
}
}
}
}
}
}
else
{
lean_object* v_a_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3853_; 
v_a_3846_ = lean_ctor_get(v___x_3818_, 0);
v_isSharedCheck_3853_ = !lean_is_exclusive(v___x_3818_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3848_ = v___x_3818_;
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_a_3846_);
lean_dec(v___x_3818_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v___x_3851_; 
if (v_isShared_3849_ == 0)
{
v___x_3851_ = v___x_3848_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_a_3846_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
return v___x_3851_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed(lean_object* v_f_3854_, lean_object* v_s_3855_, lean_object* v_a_3856_, lean_object* v_b_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_){
_start:
{
lean_object* v_res_3863_; 
v_res_3863_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0(v_f_3854_, v_s_3855_, v_a_3856_, v_b_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
lean_dec(v___y_3861_);
lean_dec_ref(v___y_3860_);
lean_dec(v___y_3859_);
lean_dec_ref(v___y_3858_);
return v_res_3863_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(lean_object* v_map_3864_, lean_object* v_init_3865_, lean_object* v_f_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_){
_start:
{
lean_object* v___f_3872_; lean_object* v___x_3873_; 
v___f_3872_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___lam__0___boxed), 9, 1);
lean_closure_set(v___f_3872_, 0, v_f_3866_);
lean_inc_ref(v_map_3864_);
v___x_3873_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v___f_3872_, v_map_3864_, v_init_3865_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3882_; 
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3882_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3882_ == 0)
{
v___x_3876_ = v___x_3873_;
v_isShared_3877_ = v_isSharedCheck_3882_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v___x_3873_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3882_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
lean_object* v_a_3878_; lean_object* v___x_3880_; 
v_a_3878_ = lean_ctor_get(v_a_3874_, 0);
lean_inc(v_a_3878_);
lean_dec(v_a_3874_);
if (v_isShared_3877_ == 0)
{
lean_ctor_set(v___x_3876_, 0, v_a_3878_);
v___x_3880_ = v___x_3876_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3881_; 
v_reuseFailAlloc_3881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3881_, 0, v_a_3878_);
v___x_3880_ = v_reuseFailAlloc_3881_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
return v___x_3880_;
}
}
}
else
{
lean_object* v_a_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3890_; 
v_a_3883_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3890_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3890_ == 0)
{
v___x_3885_ = v___x_3873_;
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_a_3883_);
lean_dec(v___x_3873_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3890_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3888_; 
if (v_isShared_3886_ == 0)
{
v___x_3888_ = v___x_3885_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v_a_3883_);
v___x_3888_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
return v___x_3888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg___boxed(lean_object* v_map_3891_, lean_object* v_init_3892_, lean_object* v_f_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
lean_object* v_res_3899_; 
v_res_3899_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_3891_, v_init_3892_, v_f_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec_ref(v_map_3891_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(lean_object* v___y_3900_){
_start:
{
lean_object* v___x_3902_; lean_object* v_env_3903_; lean_object* v___x_3904_; lean_object* v_ext_3905_; lean_object* v_toEnvExtension_3906_; lean_object* v_asyncMode_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v_categories_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___x_3902_ = lean_st_ref_get(v___y_3900_);
v_env_3903_ = lean_ctor_get(v___x_3902_, 0);
lean_inc_ref_n(v_env_3903_, 2);
lean_dec(v___x_3902_);
v___x_3904_ = l_Lean_Parser_parserExtension;
v_ext_3905_ = lean_ctor_get(v___x_3904_, 1);
v_toEnvExtension_3906_ = lean_ctor_get(v_ext_3905_, 0);
v_asyncMode_3907_ = lean_ctor_get(v_toEnvExtension_3906_, 2);
v___x_3908_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
v___x_3909_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3908_, v___x_3904_, v_env_3903_, v_asyncMode_3907_);
v_categories_3910_ = lean_ctor_get(v___x_3909_, 2);
lean_inc_ref(v_categories_3910_);
lean_dec(v___x_3909_);
v___x_3911_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_3912_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_3910_, v___x_3911_);
lean_dec_ref(v_categories_3910_);
if (lean_obj_tag(v___x_3912_) == 1)
{
lean_object* v_val_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3950_; 
v_val_3913_ = lean_ctor_get(v___x_3912_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3912_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3915_ = v___x_3912_;
v_isShared_3916_ = v_isSharedCheck_3950_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_val_3913_);
lean_dec(v___x_3912_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3950_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___y_3918_; lean_object* v___x_3927_; lean_object* v_toEnvExtension_3928_; lean_object* v_exportEntriesFn_3929_; lean_object* v_asyncMode_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v_importedEntries_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v_exported_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; uint8_t v___x_3942_; 
v___x_3927_ = l_Lean_Parser_Tactic_Doc_tacticNameExt;
v_toEnvExtension_3928_ = lean_ctor_get(v___x_3927_, 0);
v_exportEntriesFn_3929_ = lean_ctor_get(v___x_3927_, 4);
v_asyncMode_3930_ = lean_ctor_get(v_toEnvExtension_3928_, 2);
v___x_3931_ = lean_box(1);
v___x_3932_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2, &l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___closed__2);
v___x_3933_ = lean_box(0);
lean_inc_ref_n(v_env_3903_, 2);
v___x_3934_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3932_, v_toEnvExtension_3928_, v_env_3903_, v_asyncMode_3930_, v___x_3933_);
v_importedEntries_3935_ = lean_ctor_get(v___x_3934_, 0);
lean_inc_ref(v_importedEntries_3935_);
lean_dec(v___x_3934_);
v___x_3936_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3931_, v___x_3927_, v_env_3903_, v_asyncMode_3930_, v___x_3933_);
lean_inc_ref(v_exportEntriesFn_3929_);
v___x_3937_ = lean_apply_2(v_exportEntriesFn_3929_, v_env_3903_, v___x_3936_);
v_exported_3938_ = lean_ctor_get(v___x_3937_, 0);
lean_inc(v_exported_3938_);
lean_dec_ref(v___x_3937_);
v___x_3939_ = lean_array_push(v_importedEntries_3935_, v_exported_3938_);
v___x_3940_ = lean_unsigned_to_nat(0u);
v___x_3941_ = lean_array_get_size(v___x_3939_);
v___x_3942_ = lean_nat_dec_lt(v___x_3940_, v___x_3941_);
if (v___x_3942_ == 0)
{
lean_dec_ref(v___x_3939_);
v___y_3918_ = v___x_3931_;
goto v___jp_3917_;
}
else
{
uint8_t v___x_3943_; 
v___x_3943_ = lean_nat_dec_le(v___x_3941_, v___x_3941_);
if (v___x_3943_ == 0)
{
if (v___x_3942_ == 0)
{
lean_dec_ref(v___x_3939_);
v___y_3918_ = v___x_3931_;
goto v___jp_3917_;
}
else
{
size_t v___x_3944_; size_t v___x_3945_; lean_object* v___x_3946_; 
v___x_3944_ = ((size_t)0ULL);
v___x_3945_ = lean_usize_of_nat(v___x_3941_);
v___x_3946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3939_, v___x_3944_, v___x_3945_, v___x_3931_);
lean_dec_ref(v___x_3939_);
v___y_3918_ = v___x_3946_;
goto v___jp_3917_;
}
}
else
{
size_t v___x_3947_; size_t v___x_3948_; lean_object* v___x_3949_; 
v___x_3947_ = ((size_t)0ULL);
v___x_3948_ = lean_usize_of_nat(v___x_3941_);
v___x_3949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__5(v___x_3939_, v___x_3947_, v___x_3948_, v___x_3931_);
lean_dec_ref(v___x_3939_);
v___y_3918_ = v___x_3949_;
goto v___jp_3917_;
}
}
v___jp_3917_:
{
lean_object* v_tables_3919_; lean_object* v_leadingTable_3920_; lean_object* v_trailingTable_3921_; lean_object* v_firstTokens_3922_; lean_object* v_firstTokens_3923_; lean_object* v___x_3925_; 
v_tables_3919_ = lean_ctor_get(v_val_3913_, 2);
v_leadingTable_3920_ = lean_ctor_get(v_tables_3919_, 0);
v_trailingTable_3921_ = lean_ctor_get(v_tables_3919_, 2);
lean_inc(v_trailingTable_3921_);
lean_inc(v_leadingTable_3920_);
lean_inc(v_val_3913_);
v_firstTokens_3922_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_3913_, v_leadingTable_3920_, v___y_3918_);
v_firstTokens_3923_ = l___private_Lean_Elab_Tactic_Doc_0__Lean_Elab_Tactic_Doc_firstTacticTokens_addFirstTokens(v_val_3913_, v_trailingTable_3921_, v_firstTokens_3922_);
if (v_isShared_3916_ == 0)
{
lean_ctor_set_tag(v___x_3915_, 0);
lean_ctor_set(v___x_3915_, 0, v_firstTokens_3923_);
v___x_3925_ = v___x_3915_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_firstTokens_3923_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
}
else
{
lean_object* v___x_3951_; lean_object* v___x_3952_; 
lean_dec(v___x_3912_);
lean_dec_ref(v_env_3903_);
v___x_3951_ = lean_box(1);
v___x_3952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3951_);
return v___x_3952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg___boxed(lean_object* v___y_3953_, lean_object* v___y_3954_){
_start:
{
lean_object* v_res_3955_; 
v_res_3955_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_3953_);
lean_dec(v___y_3953_);
return v_res_3955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs(uint8_t v_includeUnnamed_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_){
_start:
{
lean_object* v___x_3964_; lean_object* v_env_3965_; lean_object* v___x_3966_; lean_object* v_toEnvExtension_3967_; lean_object* v_exportEntriesFn_3968_; lean_object* v_asyncMode_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v_importedEntries_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v_exported_3977_; lean_object* v___x_3978_; size_t v_sz_3979_; size_t v___x_3980_; lean_object* v___x_3981_; 
v___x_3964_ = lean_st_ref_get(v_a_3962_);
v_env_3965_ = lean_ctor_get(v___x_3964_, 0);
lean_inc_ref_n(v_env_3965_, 4);
lean_dec(v___x_3964_);
v___x_3966_ = l_Lean_Parser_Tactic_Doc_tacticTagExt;
v_toEnvExtension_3967_ = lean_ctor_get(v___x_3966_, 0);
v_exportEntriesFn_3968_ = lean_ctor_get(v___x_3966_, 4);
v_asyncMode_3969_ = lean_ctor_get(v_toEnvExtension_3967_, 2);
v___x_3970_ = lean_box(1);
v___x_3971_ = lean_obj_once(&l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0, &l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Doc_elabPrintTacTags___redArg___closed__0);
v___x_3972_ = lean_box(0);
v___x_3973_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_3971_, v_toEnvExtension_3967_, v_env_3965_, v_asyncMode_3969_, v___x_3972_);
v_importedEntries_3974_ = lean_ctor_get(v___x_3973_, 0);
lean_inc_ref(v_importedEntries_3974_);
lean_dec(v___x_3973_);
v___x_3975_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3970_, v___x_3966_, v_env_3965_, v_asyncMode_3969_, v___x_3972_);
lean_inc_ref(v_exportEntriesFn_3968_);
v___x_3976_ = lean_apply_2(v_exportEntriesFn_3968_, v_env_3965_, v___x_3975_);
v_exported_3977_ = lean_ctor_get(v___x_3976_, 0);
lean_inc(v_exported_3977_);
lean_dec_ref(v___x_3976_);
v___x_3978_ = lean_array_push(v_importedEntries_3974_, v_exported_3977_);
v_sz_3979_ = lean_array_size(v___x_3978_);
v___x_3980_ = ((size_t)0ULL);
v___x_3981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__1(v___x_3978_, v_sz_3979_, v___x_3980_, v___x_3970_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_);
lean_dec_ref(v___x_3978_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_4006_; 
v_a_3982_ = lean_ctor_get(v___x_3981_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_3984_ = v___x_3981_;
v_isShared_3985_ = v_isSharedCheck_4006_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3981_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_4006_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3986_; lean_object* v_ext_3987_; lean_object* v_toEnvExtension_3988_; lean_object* v_asyncMode_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v_categories_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3986_ = l_Lean_Parser_parserExtension;
v_ext_3987_ = lean_ctor_get(v___x_3986_, 1);
v_toEnvExtension_3988_ = lean_ctor_get(v_ext_3987_, 0);
v_asyncMode_3989_ = lean_ctor_get(v_toEnvExtension_3988_, 2);
v___x_3990_ = l_Lean_Parser_ParserExtension_instInhabitedState_default;
lean_inc_ref(v_env_3965_);
v___x_3991_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_3990_, v___x_3986_, v_env_3965_, v_asyncMode_3989_);
v_categories_3992_ = lean_ctor_get(v___x_3991_, 2);
lean_inc_ref(v_categories_3992_);
lean_dec(v___x_3991_);
v___x_3993_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___closed__0));
v___x_3994_ = ((lean_object*)(l_Lean_Elab_Tactic_Doc_firstTacticTokens___redArg___lam__2___closed__1));
v___x_3995_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_elabPrintTacTags_spec__3_spec__4___redArg(v_categories_3992_, v___x_3994_);
lean_dec_ref(v_categories_3992_);
if (lean_obj_tag(v___x_3995_) == 1)
{
lean_object* v_val_3996_; lean_object* v___x_3997_; lean_object* v_a_3998_; lean_object* v_kinds_3999_; lean_object* v___x_4000_; lean_object* v___f_4001_; lean_object* v___x_4002_; 
lean_del_object(v___x_3984_);
v_val_3996_ = lean_ctor_get(v___x_3995_, 0);
lean_inc(v_val_3996_);
lean_dec_ref(v___x_3995_);
v___x_3997_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v_a_3962_);
v_a_3998_ = lean_ctor_get(v___x_3997_, 0);
lean_inc(v_a_3998_);
lean_dec_ref(v___x_3997_);
v_kinds_3999_ = lean_ctor_get(v_val_3996_, 1);
lean_inc_ref(v_kinds_3999_);
lean_dec(v_val_3996_);
v___x_4000_ = lean_box(v_includeUnnamed_3958_);
v___f_4001_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Doc_allTacticDocs___lam__0___boxed), 11, 4);
lean_closure_set(v___f_4001_, 0, v_env_3965_);
lean_closure_set(v___f_4001_, 1, v_a_3982_);
lean_closure_set(v___f_4001_, 2, v_a_3998_);
lean_closure_set(v___f_4001_, 3, v___x_4000_);
v___x_4002_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_kinds_3999_, v___x_3993_, v___f_4001_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_);
lean_dec_ref(v_kinds_3999_);
return v___x_4002_;
}
else
{
lean_object* v___x_4004_; 
lean_dec(v___x_3995_);
lean_dec(v_a_3982_);
lean_dec_ref(v_env_3965_);
if (v_isShared_3985_ == 0)
{
lean_ctor_set(v___x_3984_, 0, v___x_3993_);
v___x_4004_ = v___x_3984_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v___x_3993_);
v___x_4004_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
return v___x_4004_;
}
}
}
}
else
{
lean_object* v_a_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4014_; 
lean_dec_ref(v_env_3965_);
v_a_4007_ = lean_ctor_get(v___x_3981_, 0);
v_isSharedCheck_4014_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_4009_ = v___x_3981_;
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_a_4007_);
lean_dec(v___x_3981_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4012_; 
if (v_isShared_4010_ == 0)
{
v___x_4012_ = v___x_4009_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_a_4007_);
v___x_4012_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
return v___x_4012_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs___boxed(lean_object* v_includeUnnamed_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_){
_start:
{
uint8_t v_includeUnnamed_boxed_4021_; lean_object* v_res_4022_; 
v_includeUnnamed_boxed_4021_ = lean_unbox(v_includeUnnamed_4015_);
v_res_4022_ = l_Lean_Elab_Tactic_Doc_allTacticDocs(v_includeUnnamed_boxed_4021_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_);
lean_dec(v_a_4019_);
lean_dec_ref(v_a_4018_);
lean_dec(v_a_4017_);
lean_dec_ref(v_a_4016_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(lean_object* v_as_4023_, size_t v_sz_4024_, size_t v_i_4025_, lean_object* v_b_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_){
_start:
{
lean_object* v___x_4032_; 
v___x_4032_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___redArg(v_as_4023_, v_sz_4024_, v_i_4025_, v_b_4026_);
return v___x_4032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0___boxed(lean_object* v_as_4033_, lean_object* v_sz_4034_, lean_object* v_i_4035_, lean_object* v_b_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_){
_start:
{
size_t v_sz_boxed_4042_; size_t v_i_boxed_4043_; lean_object* v_res_4044_; 
v_sz_boxed_4042_ = lean_unbox_usize(v_sz_4034_);
lean_dec(v_sz_4034_);
v_i_boxed_4043_ = lean_unbox_usize(v_i_4035_);
lean_dec(v_i_4035_);
v_res_4044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__0(v_as_4033_, v_sz_boxed_4042_, v_i_boxed_4043_, v_b_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_);
lean_dec(v___y_4040_);
lean_dec_ref(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec_ref(v___y_4037_);
lean_dec_ref(v_as_4033_);
return v_res_4044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_){
_start:
{
lean_object* v___x_4050_; 
v___x_4050_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___redArg(v___y_4048_);
return v___x_4050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2___boxed(lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_){
_start:
{
lean_object* v_res_4056_; 
v_res_4056_ = l_Lean_Elab_Tactic_Doc_firstTacticTokens___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__2(v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_);
lean_dec(v___y_4054_);
lean_dec_ref(v___y_4053_);
lean_dec(v___y_4052_);
lean_dec_ref(v___y_4051_);
return v_res_4056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(lean_object* v_00_u03c3_4057_, lean_object* v_00_u03b2_4058_, lean_object* v_map_4059_, lean_object* v_init_4060_, lean_object* v_f_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_){
_start:
{
lean_object* v___x_4067_; 
v___x_4067_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___redArg(v_map_4059_, v_init_4060_, v_f_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3___boxed(lean_object* v_00_u03c3_4068_, lean_object* v_00_u03b2_4069_, lean_object* v_map_4070_, lean_object* v_init_4071_, lean_object* v_f_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_){
_start:
{
lean_object* v_res_4078_; 
v_res_4078_ = l_Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3(v_00_u03c3_4068_, v_00_u03b2_4069_, v_map_4070_, v_init_4071_, v_f_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
lean_dec(v___y_4074_);
lean_dec_ref(v___y_4073_);
lean_dec_ref(v_map_4070_);
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(lean_object* v_map_4079_, lean_object* v_f_4080_, lean_object* v_init_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_){
_start:
{
lean_object* v___x_4087_; 
v___x_4087_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_4080_, v_map_4079_, v_init_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_);
return v___x_4087_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg___boxed(lean_object* v_map_4088_, lean_object* v_f_4089_, lean_object* v_init_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_){
_start:
{
lean_object* v_res_4096_; 
v_res_4096_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___redArg(v_map_4088_, v_f_4089_, v_init_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_);
lean_dec(v___y_4094_);
lean_dec_ref(v___y_4093_);
lean_dec(v___y_4092_);
lean_dec_ref(v___y_4091_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(lean_object* v_00_u03c3_4097_, lean_object* v_00_u03c3_4098_, lean_object* v_00_u03b2_4099_, lean_object* v_map_4100_, lean_object* v_f_4101_, lean_object* v_init_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_){
_start:
{
lean_object* v___x_4108_; 
v___x_4108_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_4101_, v_map_4100_, v_init_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_);
return v___x_4108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3___boxed(lean_object* v_00_u03c3_4109_, lean_object* v_00_u03c3_4110_, lean_object* v_00_u03b2_4111_, lean_object* v_map_4112_, lean_object* v_f_4113_, lean_object* v_init_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_){
_start:
{
lean_object* v_res_4120_; 
v_res_4120_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3(v_00_u03c3_4109_, v_00_u03c3_4110_, v_00_u03b2_4111_, v_map_4112_, v_f_4113_, v_init_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_);
lean_dec(v___y_4118_);
lean_dec_ref(v___y_4117_);
lean_dec(v___y_4116_);
lean_dec_ref(v___y_4115_);
return v_res_4120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(lean_object* v_00_u03c3_4121_, lean_object* v_00_u03c3_4122_, lean_object* v_00_u03b1_4123_, lean_object* v_00_u03b2_4124_, lean_object* v_f_4125_, lean_object* v_x_4126_, lean_object* v_x_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_){
_start:
{
lean_object* v___x_4133_; 
v___x_4133_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___redArg(v_f_4125_, v_x_4126_, v_x_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
return v___x_4133_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03c3_4134_, lean_object* v_00_u03c3_4135_, lean_object* v_00_u03b1_4136_, lean_object* v_00_u03b2_4137_, lean_object* v_f_4138_, lean_object* v_x_4139_, lean_object* v_x_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4(v_00_u03c3_4134_, v_00_u03c3_4135_, v_00_u03b1_4136_, v_00_u03b2_4137_, v_f_4138_, v_x_4139_, v_x_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_);
lean_dec(v___y_4144_);
lean_dec_ref(v___y_4143_);
lean_dec(v___y_4142_);
lean_dec_ref(v___y_4141_);
return v_res_4146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(lean_object* v_00_u03b1_4147_, lean_object* v_00_u03b2_4148_, lean_object* v_00_u03c3_4149_, lean_object* v_00_u03c3_4150_, lean_object* v_f_4151_, lean_object* v_as_4152_, size_t v_i_4153_, size_t v_stop_4154_, lean_object* v_b_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_){
_start:
{
lean_object* v___x_4161_; 
v___x_4161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___redArg(v_f_4151_, v_as_4152_, v_i_4153_, v_stop_4154_, v_b_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_);
return v___x_4161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b1_4162_, lean_object* v_00_u03b2_4163_, lean_object* v_00_u03c3_4164_, lean_object* v_00_u03c3_4165_, lean_object* v_f_4166_, lean_object* v_as_4167_, lean_object* v_i_4168_, lean_object* v_stop_4169_, lean_object* v_b_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_){
_start:
{
size_t v_i_boxed_4176_; size_t v_stop_boxed_4177_; lean_object* v_res_4178_; 
v_i_boxed_4176_ = lean_unbox_usize(v_i_4168_);
lean_dec(v_i_4168_);
v_stop_boxed_4177_ = lean_unbox_usize(v_stop_4169_);
lean_dec(v_stop_4169_);
v_res_4178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__5(v_00_u03b1_4162_, v_00_u03b2_4163_, v_00_u03c3_4164_, v_00_u03c3_4165_, v_f_4166_, v_as_4167_, v_i_boxed_4176_, v_stop_boxed_4177_, v_b_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
lean_dec_ref(v_as_4167_);
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(lean_object* v_00_u03c3_4179_, lean_object* v_00_u03c3_4180_, lean_object* v_00_u03b1_4181_, lean_object* v_00_u03b2_4182_, lean_object* v_f_4183_, lean_object* v_keys_4184_, lean_object* v_vals_4185_, lean_object* v_heq_4186_, lean_object* v_i_4187_, lean_object* v_acc_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_){
_start:
{
lean_object* v___x_4194_; 
v___x_4194_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___redArg(v_f_4183_, v_keys_4184_, v_vals_4185_, v_i_4187_, v_acc_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
return v___x_4194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03c3_4195_, lean_object* v_00_u03c3_4196_, lean_object* v_00_u03b1_4197_, lean_object* v_00_u03b2_4198_, lean_object* v_f_4199_, lean_object* v_keys_4200_, lean_object* v_vals_4201_, lean_object* v_heq_4202_, lean_object* v_i_4203_, lean_object* v_acc_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_){
_start:
{
lean_object* v_res_4210_; 
v_res_4210_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00Lean_Elab_Tactic_Doc_allTacticDocs_spec__3_spec__3_spec__4_spec__6(v_00_u03c3_4195_, v_00_u03c3_4196_, v_00_u03b1_4197_, v_00_u03b2_4198_, v_f_4199_, v_keys_4200_, v_vals_4201_, v_heq_4202_, v_i_4203_, v_acc_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_);
lean_dec(v___y_4208_);
lean_dec_ref(v___y_4207_);
lean_dec(v___y_4206_);
lean_dec_ref(v___y_4205_);
lean_dec_ref(v_vals_4201_);
lean_dec_ref(v_keys_4200_);
return v_res_4210_;
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
