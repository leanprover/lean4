// Lean compiler output
// Module: Lean.Server.Utils
// Imports: public import Init.System.Uri public import Lean.Data.Lsp.Communication public import Lean.Data.Lsp.Diagnostics public import Lean.Data.Lsp.Extra public import Lean.Elab.InfoTree.Util
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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_FileMap_lspPosToUtf8Pos(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_crlfToLf(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_String_toFileMap(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_System_Uri_fileUriToPath_x3f(lean_object*);
lean_object* l_System_FilePath_extension(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_getSrcSearchPath();
lean_object* l_Lean_searchModuleNameOfFileName(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap_default;
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_Lean_SearchPath_findModuleWithExt(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_realpath(lean_object*);
lean_object* l_System_Uri_pathToUri(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_throwServerError___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_throwServerError___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_throwServerError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_throwServerError___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainRight___lam__0(lean_object*, lean_object*, uint8_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainRight___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainRight___lam__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainRight___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainRight___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainRight___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainRight(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainRight___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainLeft___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainLeft___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainLeft___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainLeft___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainLeft___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainLeft___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainLeft(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainLeft___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_withPrefix___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_withPrefix___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_withPrefix___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_withPrefix___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_withPrefix(lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_instInhabitedDocumentMeta_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Server_instInhabitedDocumentMeta_default___closed__0 = (const lean_object*)&l_Lean_Server_instInhabitedDocumentMeta_default___closed__0_value;
static lean_once_cell_t l_Lean_Server_instInhabitedDocumentMeta_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_instInhabitedDocumentMeta_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedDocumentMeta_default;
LEAN_EXPORT lean_object* l_Lean_Server_instInhabitedDocumentMeta;
LEAN_EXPORT lean_object* l_Lean_Server_DocumentMeta_mkInputContext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_replaceLspRange(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_replaceLspRange___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_applyDocumentChange(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_applyDocumentChange___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_foldDocumentChanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_foldDocumentChanges___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Server_mkPublishDiagnosticsNotification_spec__0(lean_object*);
static const lean_string_object l_Lean_Server_mkPublishDiagnosticsNotification___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "textDocument/publishDiagnostics"};
static const lean_object* l_Lean_Server_mkPublishDiagnosticsNotification___closed__0 = (const lean_object*)&l_Lean_Server_mkPublishDiagnosticsNotification___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_mkPublishDiagnosticsNotification(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_mkFileProgressNotification___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "$/lean/fileProgress"};
static const lean_object* l_Lean_Server_mkFileProgressNotification___closed__0 = (const lean_object*)&l_Lean_Server_mkFileProgressNotification___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressNotification(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressNotification___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressAtPosNotification(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressAtPosNotification___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Server_mkFileProgressDoneNotification___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_mkFileProgressDoneNotification___closed__0 = (const lean_object*)&l_Lean_Server_mkFileProgressDoneNotification___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressDoneNotification(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressDoneNotification___boxed(lean_object*);
static const lean_string_object l_Lean_Server_mkApplyWorkspaceEditRequest___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "workspace/applyEdit"};
static const lean_object* l_Lean_Server_mkApplyWorkspaceEditRequest___closed__0 = (const lean_object*)&l_Lean_Server_mkApplyWorkspaceEditRequest___closed__0_value;
static const lean_ctor_object l_Lean_Server_mkApplyWorkspaceEditRequest___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_mkApplyWorkspaceEditRequest___closed__0_value)}};
static const lean_object* l_Lean_Server_mkApplyWorkspaceEditRequest___closed__1 = (const lean_object*)&l_Lean_Server_mkApplyWorkspaceEditRequest___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_mkApplyWorkspaceEditRequest(lean_object*);
static const lean_string_object l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "external:"};
static const lean_object* l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0 = (const lean_object*)&l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f(lean_object*);
static const lean_string_object l_Lean_Server_documentUriFromModule_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_Server_documentUriFromModule_x3f___closed__0 = (const lean_object*)&l_Lean_Server_documentUriFromModule_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_documentUriFromModule_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_documentUriFromModule_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Server_moduleFromDocumentUri_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Server_moduleFromDocumentUri_spec__0___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Server_moduleFromDocumentUri___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_documentUriFromModule_x3f___closed__0_value)}};
static const lean_object* l_Lean_Server_moduleFromDocumentUri___closed__0 = (const lean_object*)&l_Lean_Server_moduleFromDocumentUri___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_moduleFromDocumentUri(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_moduleFromDocumentUri___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_toLspRange(lean_object*, lean_object*);
lean_object* l_Lean_IO_throwServerError___redArg(lean_object* v_err_1_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_mk_io_user_error(v_err_1_);
v___x_4_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4_, 0, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT void l_Lean_IO_throwServerError___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_err_1_ = stack[0].m_obj;
lean_object* v_res_5_;
v_res_5_ = l_Lean_IO_throwServerError___redArg(v_err_1_);
stack->m_obj
 = v_res_5_;
}
LEAN_EXPORT lean_object* l_Lean_IO_throwServerError___redArg___boxed(lean_object* v_err_6_, lean_object* v_a_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_IO_throwServerError___redArg(v_err_6_);
return v_res_8_;
}
}
lean_object* l_Lean_IO_throwServerError(lean_object* v_00_u03b1_9_, lean_object* v_err_10_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l_Lean_IO_throwServerError___redArg(v_err_10_);
return v___x_12_;
}
}
LEAN_EXPORT void l_Lean_IO_throwServerError_0interp(lean_interpreter_value* stack)
{
lean_object* v_err_10_ = stack[1].m_obj;
lean_object* v_res_13_;
v_res_13_ = l_Lean_IO_throwServerError(lean_box(0), v_err_10_);
stack->m_obj
 = v_res_13_;
}
LEAN_EXPORT lean_object* l_Lean_IO_throwServerError___boxed(lean_object* v_00_u03b1_14_, lean_object* v_err_15_, lean_object* v_a_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Lean_IO_throwServerError(v_00_u03b1_14_, v_err_15_);
return v_res_17_;
}
}
lean_object* l_Lean_IO_FS_Stream_chainRight___lam__0(lean_object* v_read_18_, lean_object* v_b_19_, uint8_t v_flushEagerly_20_, size_t v_sz_21_){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = lean_box_usize(v_sz_21_);
v___x_24_ = lean_apply_2(v_read_18_, v___x_23_, lean_box(0));
if (lean_obj_tag(v___x_24_) == 0)
{
lean_object* v_a_25_; lean_object* v_flush_26_; lean_object* v_write_27_; lean_object* v___x_28_; 
v_a_25_ = lean_ctor_get(v___x_24_, 0);
lean_inc_n(v_a_25_, 2);
lean_dec_ref_known(v___x_24_, 1);
v_flush_26_ = lean_ctor_get(v_b_19_, 0);
lean_inc_ref(v_flush_26_);
v_write_27_ = lean_ctor_get(v_b_19_, 2);
lean_inc_ref(v_write_27_);
lean_dec_ref(v_b_19_);
v___x_28_ = lean_apply_2(v_write_27_, v_a_25_, lean_box(0));
if (lean_obj_tag(v___x_28_) == 0)
{
lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_52_; 
v_isSharedCheck_52_ = !lean_is_exclusive(v___x_28_);
if (v_isSharedCheck_52_ == 0)
{
lean_object* v_unused_53_; 
v_unused_53_ = lean_ctor_get(v___x_28_, 0);
lean_dec(v_unused_53_);
v___x_30_ = v___x_28_;
v_isShared_31_ = v_isSharedCheck_52_;
goto v_resetjp_29_;
}
else
{
lean_dec(v___x_28_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_52_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
if (v_flushEagerly_20_ == 0)
{
lean_object* v___x_33_; 
lean_dec_ref(v_flush_26_);
if (v_isShared_31_ == 0)
{
lean_ctor_set(v___x_30_, 0, v_a_25_);
v___x_33_ = v___x_30_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v_a_25_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
return v___x_33_;
}
}
else
{
lean_object* v___x_35_; 
lean_del_object(v___x_30_);
v___x_35_ = lean_apply_1(v_flush_26_, lean_box(0));
if (lean_obj_tag(v___x_35_) == 0)
{
lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_42_; 
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_35_);
if (v_isSharedCheck_42_ == 0)
{
lean_object* v_unused_43_; 
v_unused_43_ = lean_ctor_get(v___x_35_, 0);
lean_dec(v_unused_43_);
v___x_37_ = v___x_35_;
v_isShared_38_ = v_isSharedCheck_42_;
goto v_resetjp_36_;
}
else
{
lean_dec(v___x_35_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_42_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_40_; 
if (v_isShared_38_ == 0)
{
lean_ctor_set(v___x_37_, 0, v_a_25_);
v___x_40_ = v___x_37_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v_a_25_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
else
{
lean_object* v_a_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_51_; 
lean_dec(v_a_25_);
v_a_44_ = lean_ctor_get(v___x_35_, 0);
v_isSharedCheck_51_ = !lean_is_exclusive(v___x_35_);
if (v_isSharedCheck_51_ == 0)
{
v___x_46_ = v___x_35_;
v_isShared_47_ = v_isSharedCheck_51_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_a_44_);
lean_dec(v___x_35_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_51_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___x_49_; 
if (v_isShared_47_ == 0)
{
v___x_49_ = v___x_46_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v_a_44_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
}
}
}
}
else
{
lean_object* v_a_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_61_; 
lean_dec_ref(v_flush_26_);
lean_dec(v_a_25_);
v_a_54_ = lean_ctor_get(v___x_28_, 0);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_28_);
if (v_isSharedCheck_61_ == 0)
{
v___x_56_ = v___x_28_;
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_a_54_);
lean_dec(v___x_28_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_61_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_59_; 
if (v_isShared_57_ == 0)
{
v___x_59_ = v___x_56_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_a_54_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
}
}
else
{
lean_dec_ref(v_b_19_);
return v___x_24_;
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_chainRight___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_read_18_ = stack[0].m_obj;
lean_object* v_b_19_ = stack[1].m_obj;
uint8_t v_flushEagerly_20_ = stack[2].m_num;
size_t v_sz_21_ = stack[3].m_num;
lean_object* v_res_62_;
v_res_62_ = l_Lean_IO_FS_Stream_chainRight___lam__0(v_read_18_, v_b_19_, v_flushEagerly_20_, v_sz_21_);
stack->m_obj
 = v_res_62_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainRight___lam__0___boxed(lean_object* v_read_63_, lean_object* v_b_64_, lean_object* v_flushEagerly_65_, lean_object* v_sz_66_, lean_object* v___y_67_){
_start:
{
uint8_t v_flushEagerly_boxed_68_; size_t v_sz_boxed_69_; lean_object* v_res_70_; 
v_flushEagerly_boxed_68_ = lean_unbox(v_flushEagerly_65_);
v_sz_boxed_69_ = lean_unbox_usize(v_sz_66_);
lean_dec(v_sz_66_);
v_res_70_ = l_Lean_IO_FS_Stream_chainRight___lam__0(v_read_63_, v_b_64_, v_flushEagerly_boxed_68_, v_sz_boxed_69_);
return v_res_70_;
}
}
lean_object* l_Lean_IO_FS_Stream_chainRight___lam__1(lean_object* v_getLine_71_, lean_object* v_b_72_, uint8_t v_flushEagerly_73_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lean_apply_1(v_getLine_71_, lean_box(0));
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v_a_76_; lean_object* v_flush_77_; lean_object* v_putStr_78_; lean_object* v___x_79_; 
v_a_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc_n(v_a_76_, 2);
lean_dec_ref_known(v___x_75_, 1);
v_flush_77_ = lean_ctor_get(v_b_72_, 0);
lean_inc_ref(v_flush_77_);
v_putStr_78_ = lean_ctor_get(v_b_72_, 4);
lean_inc_ref(v_putStr_78_);
lean_dec_ref(v_b_72_);
v___x_79_ = lean_apply_2(v_putStr_78_, v_a_76_, lean_box(0));
if (lean_obj_tag(v___x_79_) == 0)
{
lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_103_; 
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_103_ == 0)
{
lean_object* v_unused_104_; 
v_unused_104_ = lean_ctor_get(v___x_79_, 0);
lean_dec(v_unused_104_);
v___x_81_ = v___x_79_;
v_isShared_82_ = v_isSharedCheck_103_;
goto v_resetjp_80_;
}
else
{
lean_dec(v___x_79_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_103_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
if (v_flushEagerly_73_ == 0)
{
lean_object* v___x_84_; 
lean_dec_ref(v_flush_77_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 0, v_a_76_);
v___x_84_ = v___x_81_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_a_76_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
return v___x_84_;
}
}
else
{
lean_object* v___x_86_; 
lean_del_object(v___x_81_);
v___x_86_ = lean_apply_1(v_flush_77_, lean_box(0));
if (lean_obj_tag(v___x_86_) == 0)
{
lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_93_; 
v_isSharedCheck_93_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_93_ == 0)
{
lean_object* v_unused_94_; 
v_unused_94_ = lean_ctor_get(v___x_86_, 0);
lean_dec(v_unused_94_);
v___x_88_ = v___x_86_;
v_isShared_89_ = v_isSharedCheck_93_;
goto v_resetjp_87_;
}
else
{
lean_dec(v___x_86_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_93_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_91_; 
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 0, v_a_76_);
v___x_91_ = v___x_88_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_a_76_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
else
{
lean_object* v_a_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_102_; 
lean_dec(v_a_76_);
v_a_95_ = lean_ctor_get(v___x_86_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_102_ == 0)
{
v___x_97_ = v___x_86_;
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_a_95_);
lean_dec(v___x_86_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_102_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_100_; 
if (v_isShared_98_ == 0)
{
v___x_100_ = v___x_97_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_a_95_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
}
}
}
else
{
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_112_; 
lean_dec_ref(v_flush_77_);
lean_dec(v_a_76_);
v_a_105_ = lean_ctor_get(v___x_79_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_112_ == 0)
{
v___x_107_ = v___x_79_;
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_79_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_110_; 
if (v_isShared_108_ == 0)
{
v___x_110_ = v___x_107_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_a_105_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
}
else
{
lean_dec_ref(v_b_72_);
return v___x_75_;
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_chainRight___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_getLine_71_ = stack[0].m_obj;
lean_object* v_b_72_ = stack[1].m_obj;
uint8_t v_flushEagerly_73_ = stack[2].m_num;
lean_object* v_res_113_;
v_res_113_ = l_Lean_IO_FS_Stream_chainRight___lam__1(v_getLine_71_, v_b_72_, v_flushEagerly_73_);
stack->m_obj
 = v_res_113_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainRight___lam__1___boxed(lean_object* v_getLine_114_, lean_object* v_b_115_, lean_object* v_flushEagerly_116_, lean_object* v___y_117_){
_start:
{
uint8_t v_flushEagerly_boxed_118_; lean_object* v_res_119_; 
v_flushEagerly_boxed_118_ = lean_unbox(v_flushEagerly_116_);
v_res_119_ = l_Lean_IO_FS_Stream_chainRight___lam__1(v_getLine_114_, v_b_115_, v_flushEagerly_boxed_118_);
return v_res_119_;
}
}
lean_object* l_Lean_IO_FS_Stream_chainRight___lam__2(lean_object* v_flush_120_, lean_object* v_b_121_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = lean_apply_1(v_flush_120_, lean_box(0));
if (lean_obj_tag(v___x_123_) == 0)
{
lean_object* v_flush_124_; lean_object* v___x_125_; 
lean_dec_ref_known(v___x_123_, 1);
v_flush_124_ = lean_ctor_get(v_b_121_, 0);
lean_inc_ref(v_flush_124_);
lean_dec_ref(v_b_121_);
v___x_125_ = lean_apply_1(v_flush_124_, lean_box(0));
return v___x_125_;
}
else
{
lean_dec_ref(v_b_121_);
return v___x_123_;
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_chainRight___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_flush_120_ = stack[0].m_obj;
lean_object* v_b_121_ = stack[1].m_obj;
lean_object* v_res_126_;
v_res_126_ = l_Lean_IO_FS_Stream_chainRight___lam__2(v_flush_120_, v_b_121_);
stack->m_obj
 = v_res_126_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainRight___lam__2___boxed(lean_object* v_flush_127_, lean_object* v_b_128_, lean_object* v___y_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_IO_FS_Stream_chainRight___lam__2(v_flush_127_, v_b_128_);
return v_res_130_;
}
}
lean_object* l_Lean_IO_FS_Stream_chainRight(lean_object* v_a_131_, lean_object* v_b_132_, uint8_t v_flushEagerly_133_){
_start:
{
lean_object* v_flush_134_; lean_object* v_read_135_; lean_object* v_write_136_; lean_object* v_getLine_137_; lean_object* v_putStr_138_; lean_object* v_isTty_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_151_; 
v_flush_134_ = lean_ctor_get(v_a_131_, 0);
v_read_135_ = lean_ctor_get(v_a_131_, 1);
v_write_136_ = lean_ctor_get(v_a_131_, 2);
v_getLine_137_ = lean_ctor_get(v_a_131_, 3);
v_putStr_138_ = lean_ctor_get(v_a_131_, 4);
v_isTty_139_ = lean_ctor_get(v_a_131_, 5);
v_isSharedCheck_151_ = !lean_is_exclusive(v_a_131_);
if (v_isSharedCheck_151_ == 0)
{
v___x_141_ = v_a_131_;
v_isShared_142_ = v_isSharedCheck_151_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_isTty_139_);
lean_inc(v_putStr_138_);
lean_inc(v_getLine_137_);
lean_inc(v_write_136_);
lean_inc(v_read_135_);
lean_inc(v_flush_134_);
lean_dec(v_a_131_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_151_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_143_; lean_object* v___f_144_; lean_object* v___x_145_; lean_object* v___f_146_; lean_object* v___f_147_; lean_object* v___x_149_; 
v___x_143_ = lean_box(v_flushEagerly_133_);
lean_inc_ref_n(v_b_132_, 2);
v___f_144_ = lean_alloc_closure((void*)(l_Lean_IO_FS_Stream_chainRight___lam__0___boxed), 5, 3);
lean_closure_set(v___f_144_, 0, v_read_135_);
lean_closure_set(v___f_144_, 1, v_b_132_);
lean_closure_set(v___f_144_, 2, v___x_143_);
v___x_145_ = lean_box(v_flushEagerly_133_);
v___f_146_ = lean_alloc_closure((void*)(l_Lean_IO_FS_Stream_chainRight___lam__1___boxed), 4, 3);
lean_closure_set(v___f_146_, 0, v_getLine_137_);
lean_closure_set(v___f_146_, 1, v_b_132_);
lean_closure_set(v___f_146_, 2, v___x_145_);
v___f_147_ = lean_alloc_closure((void*)(l_Lean_IO_FS_Stream_chainRight___lam__2___boxed), 3, 2);
lean_closure_set(v___f_147_, 0, v_flush_134_);
lean_closure_set(v___f_147_, 1, v_b_132_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 3, v___f_146_);
lean_ctor_set(v___x_141_, 1, v___f_144_);
lean_ctor_set(v___x_141_, 0, v___f_147_);
v___x_149_ = v___x_141_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___f_147_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v___f_144_);
lean_ctor_set(v_reuseFailAlloc_150_, 2, v_write_136_);
lean_ctor_set(v_reuseFailAlloc_150_, 3, v___f_146_);
lean_ctor_set(v_reuseFailAlloc_150_, 4, v_putStr_138_);
lean_ctor_set(v_reuseFailAlloc_150_, 5, v_isTty_139_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_chainRight_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_131_ = stack[0].m_obj;
lean_object* v_b_132_ = stack[1].m_obj;
uint8_t v_flushEagerly_133_ = stack[2].m_num;
lean_object* v_res_152_;
v_res_152_ = l_Lean_IO_FS_Stream_chainRight(v_a_131_, v_b_132_, v_flushEagerly_133_);
stack->m_obj
 = v_res_152_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainRight___boxed(lean_object* v_a_153_, lean_object* v_b_154_, lean_object* v_flushEagerly_155_){
_start:
{
uint8_t v_flushEagerly_boxed_156_; lean_object* v_res_157_; 
v_flushEagerly_boxed_156_ = lean_unbox(v_flushEagerly_155_);
v_res_157_ = l_Lean_IO_FS_Stream_chainRight(v_a_153_, v_b_154_, v_flushEagerly_boxed_156_);
return v_res_157_;
}
}
lean_object* l_Lean_IO_FS_Stream_chainLeft___lam__0(lean_object* v_flush_158_, lean_object* v_flush_159_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = lean_apply_1(v_flush_158_, lean_box(0));
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v___x_162_; 
lean_dec_ref_known(v___x_161_, 1);
v___x_162_ = lean_apply_1(v_flush_159_, lean_box(0));
return v___x_162_;
}
else
{
lean_dec_ref(v_flush_159_);
return v___x_161_;
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_chainLeft___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_flush_158_ = stack[0].m_obj;
lean_object* v_flush_159_ = stack[1].m_obj;
lean_object* v_res_163_;
v_res_163_ = l_Lean_IO_FS_Stream_chainLeft___lam__0(v_flush_158_, v_flush_159_);
stack->m_obj
 = v_res_163_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainLeft___lam__0___boxed(lean_object* v_flush_164_, lean_object* v_flush_165_, lean_object* v___y_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_IO_FS_Stream_chainLeft___lam__0(v_flush_164_, v_flush_165_);
return v_res_167_;
}
}
lean_object* l_Lean_IO_FS_Stream_chainLeft___lam__1(lean_object* v_write_168_, uint8_t v_flushEagerly_169_, lean_object* v_write_170_, lean_object* v_flush_171_, lean_object* v_bs_172_){
_start:
{
lean_object* v___x_174_; 
lean_inc_ref(v_bs_172_);
v___x_174_ = lean_apply_2(v_write_168_, v_bs_172_, lean_box(0));
if (lean_obj_tag(v___x_174_) == 0)
{
lean_dec_ref_known(v___x_174_, 1);
if (v_flushEagerly_169_ == 0)
{
lean_object* v___x_175_; 
lean_dec_ref(v_flush_171_);
v___x_175_ = lean_apply_2(v_write_170_, v_bs_172_, lean_box(0));
return v___x_175_;
}
else
{
lean_object* v___x_176_; 
v___x_176_ = lean_apply_1(v_flush_171_, lean_box(0));
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v___x_177_; 
lean_dec_ref_known(v___x_176_, 1);
v___x_177_ = lean_apply_2(v_write_170_, v_bs_172_, lean_box(0));
return v___x_177_;
}
else
{
lean_dec_ref(v_bs_172_);
lean_dec_ref(v_write_170_);
return v___x_176_;
}
}
}
else
{
lean_dec_ref(v_bs_172_);
lean_dec_ref(v_flush_171_);
lean_dec_ref(v_write_170_);
return v___x_174_;
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_chainLeft___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_write_168_ = stack[0].m_obj;
uint8_t v_flushEagerly_169_ = stack[1].m_num;
lean_object* v_write_170_ = stack[2].m_obj;
lean_object* v_flush_171_ = stack[3].m_obj;
lean_object* v_bs_172_ = stack[4].m_obj;
lean_object* v_res_178_;
v_res_178_ = l_Lean_IO_FS_Stream_chainLeft___lam__1(v_write_168_, v_flushEagerly_169_, v_write_170_, v_flush_171_, v_bs_172_);
stack->m_obj
 = v_res_178_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainLeft___lam__1___boxed(lean_object* v_write_179_, lean_object* v_flushEagerly_180_, lean_object* v_write_181_, lean_object* v_flush_182_, lean_object* v_bs_183_, lean_object* v___y_184_){
_start:
{
uint8_t v_flushEagerly_boxed_185_; lean_object* v_res_186_; 
v_flushEagerly_boxed_185_ = lean_unbox(v_flushEagerly_180_);
v_res_186_ = l_Lean_IO_FS_Stream_chainLeft___lam__1(v_write_179_, v_flushEagerly_boxed_185_, v_write_181_, v_flush_182_, v_bs_183_);
return v_res_186_;
}
}
lean_object* l_Lean_IO_FS_Stream_chainLeft___lam__2(lean_object* v_putStr_187_, uint8_t v_flushEagerly_188_, lean_object* v_putStr_189_, lean_object* v_flush_190_, lean_object* v_s_191_){
_start:
{
lean_object* v___x_193_; 
lean_inc_ref(v_s_191_);
v___x_193_ = lean_apply_2(v_putStr_187_, v_s_191_, lean_box(0));
if (lean_obj_tag(v___x_193_) == 0)
{
lean_dec_ref_known(v___x_193_, 1);
if (v_flushEagerly_188_ == 0)
{
lean_object* v___x_194_; 
lean_dec_ref(v_flush_190_);
v___x_194_ = lean_apply_2(v_putStr_189_, v_s_191_, lean_box(0));
return v___x_194_;
}
else
{
lean_object* v___x_195_; 
v___x_195_ = lean_apply_1(v_flush_190_, lean_box(0));
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v___x_196_; 
lean_dec_ref_known(v___x_195_, 1);
v___x_196_ = lean_apply_2(v_putStr_189_, v_s_191_, lean_box(0));
return v___x_196_;
}
else
{
lean_dec_ref(v_s_191_);
lean_dec_ref(v_putStr_189_);
return v___x_195_;
}
}
}
else
{
lean_dec_ref(v_s_191_);
lean_dec_ref(v_flush_190_);
lean_dec_ref(v_putStr_189_);
return v___x_193_;
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_chainLeft___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_putStr_187_ = stack[0].m_obj;
uint8_t v_flushEagerly_188_ = stack[1].m_num;
lean_object* v_putStr_189_ = stack[2].m_obj;
lean_object* v_flush_190_ = stack[3].m_obj;
lean_object* v_s_191_ = stack[4].m_obj;
lean_object* v_res_197_;
v_res_197_ = l_Lean_IO_FS_Stream_chainLeft___lam__2(v_putStr_187_, v_flushEagerly_188_, v_putStr_189_, v_flush_190_, v_s_191_);
stack->m_obj
 = v_res_197_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainLeft___lam__2___boxed(lean_object* v_putStr_198_, lean_object* v_flushEagerly_199_, lean_object* v_putStr_200_, lean_object* v_flush_201_, lean_object* v_s_202_, lean_object* v___y_203_){
_start:
{
uint8_t v_flushEagerly_boxed_204_; lean_object* v_res_205_; 
v_flushEagerly_boxed_204_ = lean_unbox(v_flushEagerly_199_);
v_res_205_ = l_Lean_IO_FS_Stream_chainLeft___lam__2(v_putStr_198_, v_flushEagerly_boxed_204_, v_putStr_200_, v_flush_201_, v_s_202_);
return v_res_205_;
}
}
lean_object* l_Lean_IO_FS_Stream_chainLeft(lean_object* v_a_206_, lean_object* v_b_207_, uint8_t v_flushEagerly_208_){
_start:
{
lean_object* v_flush_209_; lean_object* v_write_210_; lean_object* v_putStr_211_; lean_object* v_flush_212_; lean_object* v_read_213_; lean_object* v_write_214_; lean_object* v_getLine_215_; lean_object* v_putStr_216_; lean_object* v_isTty_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_229_; 
v_flush_209_ = lean_ctor_get(v_a_206_, 0);
lean_inc_ref(v_flush_209_);
v_write_210_ = lean_ctor_get(v_a_206_, 2);
lean_inc_ref(v_write_210_);
v_putStr_211_ = lean_ctor_get(v_a_206_, 4);
lean_inc_ref(v_putStr_211_);
lean_dec_ref(v_a_206_);
v_flush_212_ = lean_ctor_get(v_b_207_, 0);
v_read_213_ = lean_ctor_get(v_b_207_, 1);
v_write_214_ = lean_ctor_get(v_b_207_, 2);
v_getLine_215_ = lean_ctor_get(v_b_207_, 3);
v_putStr_216_ = lean_ctor_get(v_b_207_, 4);
v_isTty_217_ = lean_ctor_get(v_b_207_, 5);
v_isSharedCheck_229_ = !lean_is_exclusive(v_b_207_);
if (v_isSharedCheck_229_ == 0)
{
v___x_219_ = v_b_207_;
v_isShared_220_ = v_isSharedCheck_229_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_isTty_217_);
lean_inc(v_putStr_216_);
lean_inc(v_getLine_215_);
lean_inc(v_write_214_);
lean_inc(v_read_213_);
lean_inc(v_flush_212_);
lean_dec(v_b_207_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_229_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___f_221_; lean_object* v___x_222_; lean_object* v___f_223_; lean_object* v___x_224_; lean_object* v___f_225_; lean_object* v___x_227_; 
lean_inc_ref_n(v_flush_209_, 2);
v___f_221_ = lean_alloc_closure((void*)(l_Lean_IO_FS_Stream_chainLeft___lam__0___boxed), 3, 2);
lean_closure_set(v___f_221_, 0, v_flush_209_);
lean_closure_set(v___f_221_, 1, v_flush_212_);
v___x_222_ = lean_box(v_flushEagerly_208_);
v___f_223_ = lean_alloc_closure((void*)(l_Lean_IO_FS_Stream_chainLeft___lam__1___boxed), 6, 4);
lean_closure_set(v___f_223_, 0, v_write_210_);
lean_closure_set(v___f_223_, 1, v___x_222_);
lean_closure_set(v___f_223_, 2, v_write_214_);
lean_closure_set(v___f_223_, 3, v_flush_209_);
v___x_224_ = lean_box(v_flushEagerly_208_);
v___f_225_ = lean_alloc_closure((void*)(l_Lean_IO_FS_Stream_chainLeft___lam__2___boxed), 6, 4);
lean_closure_set(v___f_225_, 0, v_putStr_211_);
lean_closure_set(v___f_225_, 1, v___x_224_);
lean_closure_set(v___f_225_, 2, v_putStr_216_);
lean_closure_set(v___f_225_, 3, v_flush_209_);
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 4, v___f_225_);
lean_ctor_set(v___x_219_, 2, v___f_223_);
lean_ctor_set(v___x_219_, 0, v___f_221_);
v___x_227_ = v___x_219_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___f_221_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_read_213_);
lean_ctor_set(v_reuseFailAlloc_228_, 2, v___f_223_);
lean_ctor_set(v_reuseFailAlloc_228_, 3, v_getLine_215_);
lean_ctor_set(v_reuseFailAlloc_228_, 4, v___f_225_);
lean_ctor_set(v_reuseFailAlloc_228_, 5, v_isTty_217_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_chainLeft_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_206_ = stack[0].m_obj;
lean_object* v_b_207_ = stack[1].m_obj;
uint8_t v_flushEagerly_208_ = stack[2].m_num;
lean_object* v_res_230_;
v_res_230_ = l_Lean_IO_FS_Stream_chainLeft(v_a_206_, v_b_207_, v_flushEagerly_208_);
stack->m_obj
 = v_res_230_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_chainLeft___boxed(lean_object* v_a_231_, lean_object* v_b_232_, lean_object* v_flushEagerly_233_){
_start:
{
uint8_t v_flushEagerly_boxed_234_; lean_object* v_res_235_; 
v_flushEagerly_boxed_234_ = lean_unbox(v_flushEagerly_233_);
v_res_235_ = l_Lean_IO_FS_Stream_chainLeft(v_a_231_, v_b_232_, v_flushEagerly_boxed_234_);
return v_res_235_;
}
}
lean_object* l_Lean_IO_FS_Stream_withPrefix___lam__0(lean_object* v_putStr_236_, lean_object* v_pre_237_, lean_object* v_write_238_, lean_object* v_bs_239_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = lean_apply_2(v_putStr_236_, v_pre_237_, lean_box(0));
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v___x_242_; 
lean_dec_ref_known(v___x_241_, 1);
v___x_242_ = lean_apply_2(v_write_238_, v_bs_239_, lean_box(0));
return v___x_242_;
}
else
{
lean_dec_ref(v_bs_239_);
lean_dec_ref(v_write_238_);
return v___x_241_;
}
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_withPrefix___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_putStr_236_ = stack[0].m_obj;
lean_object* v_pre_237_ = stack[1].m_obj;
lean_object* v_write_238_ = stack[2].m_obj;
lean_object* v_bs_239_ = stack[3].m_obj;
lean_object* v_res_243_;
v_res_243_ = l_Lean_IO_FS_Stream_withPrefix___lam__0(v_putStr_236_, v_pre_237_, v_write_238_, v_bs_239_);
stack->m_obj
 = v_res_243_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_withPrefix___lam__0___boxed(lean_object* v_putStr_244_, lean_object* v_pre_245_, lean_object* v_write_246_, lean_object* v_bs_247_, lean_object* v___y_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_Lean_IO_FS_Stream_withPrefix___lam__0(v_putStr_244_, v_pre_245_, v_write_246_, v_bs_247_);
return v_res_249_;
}
}
lean_object* l_Lean_IO_FS_Stream_withPrefix___lam__1(lean_object* v_pre_250_, lean_object* v_putStr_251_, lean_object* v_s_252_){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_string_append(v_pre_250_, v_s_252_);
v___x_255_ = lean_apply_2(v_putStr_251_, v___x_254_, lean_box(0));
return v___x_255_;
}
}
LEAN_EXPORT void l_Lean_IO_FS_Stream_withPrefix___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_pre_250_ = stack[0].m_obj;
lean_object* v_putStr_251_ = stack[1].m_obj;
lean_object* v_s_252_ = stack[2].m_obj;
lean_object* v_res_256_;
v_res_256_ = l_Lean_IO_FS_Stream_withPrefix___lam__1(v_pre_250_, v_putStr_251_, v_s_252_);
stack->m_obj
 = v_res_256_;
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_withPrefix___lam__1___boxed(lean_object* v_pre_257_, lean_object* v_putStr_258_, lean_object* v_s_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_IO_FS_Stream_withPrefix___lam__1(v_pre_257_, v_putStr_258_, v_s_259_);
lean_dec_ref(v_s_259_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_IO_FS_Stream_withPrefix(lean_object* v_a_262_, lean_object* v_pre_263_){
_start:
{
lean_object* v_flush_264_; lean_object* v_read_265_; lean_object* v_write_266_; lean_object* v_getLine_267_; lean_object* v_putStr_268_; lean_object* v_isTty_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_278_; 
v_flush_264_ = lean_ctor_get(v_a_262_, 0);
v_read_265_ = lean_ctor_get(v_a_262_, 1);
v_write_266_ = lean_ctor_get(v_a_262_, 2);
v_getLine_267_ = lean_ctor_get(v_a_262_, 3);
v_putStr_268_ = lean_ctor_get(v_a_262_, 4);
v_isTty_269_ = lean_ctor_get(v_a_262_, 5);
v_isSharedCheck_278_ = !lean_is_exclusive(v_a_262_);
if (v_isSharedCheck_278_ == 0)
{
v___x_271_ = v_a_262_;
v_isShared_272_ = v_isSharedCheck_278_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_isTty_269_);
lean_inc(v_putStr_268_);
lean_inc(v_getLine_267_);
lean_inc(v_write_266_);
lean_inc(v_read_265_);
lean_inc(v_flush_264_);
lean_dec(v_a_262_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_278_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___f_273_; lean_object* v___f_274_; lean_object* v___x_276_; 
lean_inc_ref(v_pre_263_);
lean_inc_ref(v_putStr_268_);
v___f_273_ = lean_alloc_closure((void*)(l_Lean_IO_FS_Stream_withPrefix___lam__0___boxed), 5, 3);
lean_closure_set(v___f_273_, 0, v_putStr_268_);
lean_closure_set(v___f_273_, 1, v_pre_263_);
lean_closure_set(v___f_273_, 2, v_write_266_);
v___f_274_ = lean_alloc_closure((void*)(l_Lean_IO_FS_Stream_withPrefix___lam__1___boxed), 4, 2);
lean_closure_set(v___f_274_, 0, v_pre_263_);
lean_closure_set(v___f_274_, 1, v_putStr_268_);
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 4, v___f_274_);
lean_ctor_set(v___x_271_, 2, v___f_273_);
v___x_276_ = v___x_271_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_flush_264_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v_read_265_);
lean_ctor_set(v_reuseFailAlloc_277_, 2, v___f_273_);
lean_ctor_set(v_reuseFailAlloc_277_, 3, v_getLine_267_);
lean_ctor_set(v_reuseFailAlloc_277_, 4, v___f_274_);
lean_ctor_set(v_reuseFailAlloc_277_, 5, v_isTty_269_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
static lean_object* _init_l_Lean_Server_instInhabitedDocumentMeta_default___closed__1(void){
_start:
{
uint8_t v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_280_ = 0;
v___x_281_ = l_Lean_instInhabitedFileMap_default;
v___x_282_ = lean_unsigned_to_nat(0u);
v___x_283_ = lean_box(0);
v___x_284_ = ((lean_object*)(l_Lean_Server_instInhabitedDocumentMeta_default___closed__0));
v___x_285_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v___x_283_);
lean_ctor_set(v___x_285_, 2, v___x_282_);
lean_ctor_set(v___x_285_, 3, v___x_281_);
lean_ctor_set_uint8(v___x_285_, sizeof(void*)*4, v___x_280_);
return v___x_285_;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedDocumentMeta_default(void){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = lean_obj_once(&l_Lean_Server_instInhabitedDocumentMeta_default___closed__1, &l_Lean_Server_instInhabitedDocumentMeta_default___closed__1_once, _init_l_Lean_Server_instInhabitedDocumentMeta_default___closed__1);
return v___x_286_;
}
}
static lean_object* _init_l_Lean_Server_instInhabitedDocumentMeta(void){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Lean_Server_instInhabitedDocumentMeta_default;
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_DocumentMeta_mkInputContext(lean_object* v_doc_288_){
_start:
{
lean_object* v_text_289_; lean_object* v_uri_290_; lean_object* v_source_291_; lean_object* v___y_293_; lean_object* v___x_296_; 
v_text_289_ = lean_ctor_get(v_doc_288_, 3);
lean_inc_ref(v_text_289_);
v_uri_290_ = lean_ctor_get(v_doc_288_, 0);
lean_inc_ref(v_uri_290_);
lean_dec_ref(v_doc_288_);
v_source_291_ = lean_ctor_get(v_text_289_, 0);
lean_inc_ref(v_source_291_);
v___x_296_ = l_System_Uri_fileUriToPath_x3f(v_uri_290_);
if (lean_obj_tag(v___x_296_) == 0)
{
v___y_293_ = v_uri_290_;
goto v___jp_292_;
}
else
{
lean_object* v_val_297_; 
lean_dec_ref(v_uri_290_);
v_val_297_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_val_297_);
lean_dec_ref_known(v___x_296_, 1);
v___y_293_ = v_val_297_;
goto v___jp_292_;
}
v___jp_292_:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_string_utf8_byte_size(v_source_291_);
v___x_295_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_295_, 0, v_source_291_);
lean_ctor_set(v___x_295_, 1, v___y_293_);
lean_ctor_set(v___x_295_, 2, v_text_289_);
lean_ctor_set(v___x_295_, 3, v___x_294_);
return v___x_295_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_replaceLspRange(lean_object* v_text_298_, lean_object* v_r_299_, lean_object* v_newText_300_){
_start:
{
lean_object* v_start_301_; lean_object* v_end_302_; lean_object* v_source_303_; lean_object* v_start_304_; lean_object* v_end_305_; lean_object* v___x_306_; lean_object* v_pre_307_; lean_object* v___x_308_; lean_object* v_post_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v_start_301_ = lean_ctor_get(v_r_299_, 0);
lean_inc_ref(v_start_301_);
v_end_302_ = lean_ctor_get(v_r_299_, 1);
lean_inc_ref(v_end_302_);
lean_dec_ref(v_r_299_);
v_source_303_ = lean_ctor_get(v_text_298_, 0);
v_start_304_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_298_, v_start_301_);
v_end_305_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_298_, v_end_302_);
v___x_306_ = lean_unsigned_to_nat(0u);
v_pre_307_ = lean_string_utf8_extract(v_source_303_, v___x_306_, v_start_304_);
lean_dec(v_start_304_);
v___x_308_ = lean_string_utf8_byte_size(v_source_303_);
v_post_309_ = lean_string_utf8_extract(v_source_303_, v_end_305_, v___x_308_);
lean_dec(v_end_305_);
v___x_310_ = l_String_crlfToLf(v_newText_300_);
v___x_311_ = lean_string_append(v_pre_307_, v___x_310_);
lean_dec_ref(v___x_310_);
v___x_312_ = lean_string_append(v___x_311_, v_post_309_);
lean_dec_ref(v_post_309_);
v___x_313_ = l_Lean_String_toFileMap(v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_replaceLspRange___boxed(lean_object* v_text_314_, lean_object* v_r_315_, lean_object* v_newText_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_Server_replaceLspRange(v_text_314_, v_r_315_, v_newText_316_);
lean_dec_ref(v_newText_316_);
lean_dec_ref(v_text_314_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_applyDocumentChange(lean_object* v_oldText_318_, lean_object* v_x_319_){
_start:
{
if (lean_obj_tag(v_x_319_) == 0)
{
lean_object* v_range_320_; lean_object* v_text_321_; lean_object* v___x_322_; 
v_range_320_ = lean_ctor_get(v_x_319_, 0);
lean_inc_ref(v_range_320_);
v_text_321_ = lean_ctor_get(v_x_319_, 1);
lean_inc_ref(v_text_321_);
lean_dec_ref_known(v_x_319_, 2);
v___x_322_ = l_Lean_Server_replaceLspRange(v_oldText_318_, v_range_320_, v_text_321_);
lean_dec_ref(v_text_321_);
return v___x_322_;
}
else
{
lean_object* v_text_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v_text_323_ = lean_ctor_get(v_x_319_, 0);
lean_inc_ref(v_text_323_);
lean_dec_ref_known(v_x_319_, 1);
v___x_324_ = l_String_crlfToLf(v_text_323_);
lean_dec_ref(v_text_323_);
v___x_325_ = l_Lean_String_toFileMap(v___x_324_);
return v___x_325_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_applyDocumentChange___boxed(lean_object* v_oldText_326_, lean_object* v_x_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_Server_applyDocumentChange(v_oldText_326_, v_x_327_);
lean_dec_ref(v_oldText_326_);
return v_res_328_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0(lean_object* v_as_329_, size_t v_i_330_, size_t v_stop_331_, lean_object* v_b_332_){
_start:
{
uint8_t v___x_333_; 
v___x_333_ = lean_usize_dec_eq(v_i_330_, v_stop_331_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; lean_object* v___x_335_; size_t v___x_336_; size_t v___x_337_; 
v___x_334_ = lean_array_uget_borrowed(v_as_329_, v_i_330_);
lean_inc(v___x_334_);
v___x_335_ = l_Lean_Server_applyDocumentChange(v_b_332_, v___x_334_);
lean_dec_ref(v_b_332_);
v___x_336_ = ((size_t)1ULL);
v___x_337_ = lean_usize_add(v_i_330_, v___x_336_);
v_i_330_ = v___x_337_;
v_b_332_ = v___x_335_;
goto _start;
}
else
{
return v_b_332_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_329_ = stack[0].m_obj;
size_t v_i_330_ = stack[1].m_num;
size_t v_stop_331_ = stack[2].m_num;
lean_object* v_b_332_ = stack[3].m_obj;
lean_object* v_res_339_;
v_res_339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0(v_as_329_, v_i_330_, v_stop_331_, v_b_332_);
stack->m_obj
 = v_res_339_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0___boxed(lean_object* v_as_340_, lean_object* v_i_341_, lean_object* v_stop_342_, lean_object* v_b_343_){
_start:
{
size_t v_i_boxed_344_; size_t v_stop_boxed_345_; lean_object* v_res_346_; 
v_i_boxed_344_ = lean_unbox_usize(v_i_341_);
lean_dec(v_i_341_);
v_stop_boxed_345_ = lean_unbox_usize(v_stop_342_);
lean_dec(v_stop_342_);
v_res_346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0(v_as_340_, v_i_boxed_344_, v_stop_boxed_345_, v_b_343_);
lean_dec_ref(v_as_340_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_foldDocumentChanges(lean_object* v_changes_347_, lean_object* v_oldText_348_){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_349_ = lean_unsigned_to_nat(0u);
v___x_350_ = lean_array_get_size(v_changes_347_);
v___x_351_ = lean_nat_dec_lt(v___x_349_, v___x_350_);
if (v___x_351_ == 0)
{
return v_oldText_348_;
}
else
{
uint8_t v___x_352_; 
v___x_352_ = lean_nat_dec_le(v___x_350_, v___x_350_);
if (v___x_352_ == 0)
{
if (v___x_351_ == 0)
{
return v_oldText_348_;
}
else
{
size_t v___x_353_; size_t v___x_354_; lean_object* v___x_355_; 
v___x_353_ = ((size_t)0ULL);
v___x_354_ = lean_usize_of_nat(v___x_350_);
v___x_355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0(v_changes_347_, v___x_353_, v___x_354_, v_oldText_348_);
return v___x_355_;
}
}
else
{
size_t v___x_356_; size_t v___x_357_; lean_object* v___x_358_; 
v___x_356_ = ((size_t)0ULL);
v___x_357_ = lean_usize_of_nat(v___x_350_);
v___x_358_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_foldDocumentChanges_spec__0(v_changes_347_, v___x_356_, v___x_357_, v_oldText_348_);
return v___x_358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_foldDocumentChanges___boxed(lean_object* v_changes_359_, lean_object* v_oldText_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_Server_foldDocumentChanges(v_changes_359_, v_oldText_360_);
lean_dec_ref(v_changes_359_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Server_mkPublishDiagnosticsNotification_spec__0(lean_object* v_a_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = lean_nat_to_int(v_a_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_mkPublishDiagnosticsNotification(lean_object* v_m_365_, lean_object* v_diagnostics_366_, lean_object* v_isIncremental_367_){
_start:
{
lean_object* v_uri_368_; lean_object* v_version_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v_uri_368_ = lean_ctor_get(v_m_365_, 0);
lean_inc_ref(v_uri_368_);
v_version_369_ = lean_ctor_get(v_m_365_, 2);
lean_inc(v_version_369_);
lean_dec_ref(v_m_365_);
v___x_370_ = ((lean_object*)(l_Lean_Server_mkPublishDiagnosticsNotification___closed__0));
v___x_371_ = lean_nat_to_int(v_version_369_);
v___x_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
v___x_373_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_373_, 0, v_uri_368_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
lean_ctor_set(v___x_373_, 2, v_isIncremental_367_);
lean_ctor_set(v___x_373_, 3, v_diagnostics_366_);
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_370_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressNotification(lean_object* v_m_376_, lean_object* v_processing_377_){
_start:
{
lean_object* v_uri_378_; lean_object* v_version_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v_uri_378_ = lean_ctor_get(v_m_376_, 0);
v_version_379_ = lean_ctor_get(v_m_376_, 2);
v___x_380_ = ((lean_object*)(l_Lean_Server_mkFileProgressNotification___closed__0));
lean_inc(v_version_379_);
v___x_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_381_, 0, v_version_379_);
lean_inc_ref(v_uri_378_);
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v_uri_378_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
v___x_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v_processing_377_);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_380_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressNotification___boxed(lean_object* v_m_385_, lean_object* v_processing_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Server_mkFileProgressNotification(v_m_385_, v_processing_386_);
lean_dec_ref(v_m_385_);
return v_res_387_;
}
}
lean_object* l_Lean_Server_mkFileProgressAtPosNotification(lean_object* v_m_388_, lean_object* v_pos_389_, uint8_t v_kind_390_){
_start:
{
lean_object* v_text_391_; lean_object* v_source_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v_text_391_ = lean_ctor_get(v_m_388_, 3);
v_source_392_ = lean_ctor_get(v_text_391_, 0);
lean_inc_ref_n(v_text_391_, 2);
v___x_393_ = l_Lean_FileMap_utf8PosToLspPos(v_text_391_, v_pos_389_);
v___x_394_ = lean_string_utf8_byte_size(v_source_392_);
v___x_395_ = l_Lean_FileMap_utf8PosToLspPos(v_text_391_, v___x_394_);
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_393_);
lean_ctor_set(v___x_396_, 1, v___x_395_);
v___x_397_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_397_, 0, v___x_396_);
lean_ctor_set_uint8(v___x_397_, sizeof(void*)*1, v_kind_390_);
v___x_398_ = lean_unsigned_to_nat(1u);
v___x_399_ = lean_mk_empty_array_with_capacity(v___x_398_);
v___x_400_ = lean_array_push(v___x_399_, v___x_397_);
v___x_401_ = l_Lean_Server_mkFileProgressNotification(v_m_388_, v___x_400_);
lean_dec_ref(v_m_388_);
return v___x_401_;
}
}
LEAN_EXPORT void l_Lean_Server_mkFileProgressAtPosNotification_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_388_ = stack[0].m_obj;
lean_object* v_pos_389_ = stack[1].m_obj;
uint8_t v_kind_390_ = stack[2].m_num;
lean_object* v_res_402_;
v_res_402_ = l_Lean_Server_mkFileProgressAtPosNotification(v_m_388_, v_pos_389_, v_kind_390_);
stack->m_obj
 = v_res_402_;
}
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressAtPosNotification___boxed(lean_object* v_m_403_, lean_object* v_pos_404_, lean_object* v_kind_405_){
_start:
{
uint8_t v_kind_boxed_406_; lean_object* v_res_407_; 
v_kind_boxed_406_ = lean_unbox(v_kind_405_);
v_res_407_ = l_Lean_Server_mkFileProgressAtPosNotification(v_m_403_, v_pos_404_, v_kind_boxed_406_);
lean_dec(v_pos_404_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressDoneNotification(lean_object* v_m_410_){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = ((lean_object*)(l_Lean_Server_mkFileProgressDoneNotification___closed__0));
v___x_412_ = l_Lean_Server_mkFileProgressNotification(v_m_410_, v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_mkFileProgressDoneNotification___boxed(lean_object* v_m_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_Server_mkFileProgressDoneNotification(v_m_413_);
lean_dec_ref(v_m_413_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_mkApplyWorkspaceEditRequest(lean_object* v_params_418_){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_419_ = ((lean_object*)(l_Lean_Server_mkApplyWorkspaceEditRequest___closed__0));
v___x_420_ = ((lean_object*)(l_Lean_Server_mkApplyWorkspaceEditRequest___closed__1));
v___x_421_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
lean_ctor_set(v___x_421_, 1, v___x_419_);
lean_ctor_set(v___x_421_, 2, v_params_418_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(lean_object* v_uri_423_){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_424_ = lean_box(0);
v___x_425_ = ((lean_object*)(l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0));
v___x_426_ = lean_string_append(v___x_425_, v_uri_423_);
v___x_427_ = l_Lean_Name_str___override(v___x_424_, v___x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___boxed(lean_object* v_uri_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(v_uri_428_);
lean_dec_ref(v_uri_428_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg(lean_object* v_s_430_){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_431_ = lean_string_utf8_byte_size(v_s_430_);
v___x_432_ = lean_unsigned_to_nat(9u);
v___x_433_ = lean_nat_dec_le(v___x_432_, v___x_431_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; 
lean_dec_ref(v_s_430_);
v___x_434_ = lean_box(0);
return v___x_434_;
}
else
{
lean_object* v___x_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_435_ = ((lean_object*)(l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName___closed__0));
v___x_436_ = lean_unsigned_to_nat(0u);
v___x_437_ = lean_string_memcmp(v_s_430_, v___x_435_, v___x_436_, v___x_436_, v___x_432_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; 
lean_dec_ref(v_s_430_);
v___x_438_ = lean_box(0);
return v___x_438_;
}
else
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
lean_inc_ref(v_s_430_);
v___x_439_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_439_, 0, v_s_430_);
lean_ctor_set(v___x_439_, 1, v___x_436_);
lean_ctor_set(v___x_439_, 2, v___x_431_);
v___x_440_ = l_String_Slice_pos_x21(v___x_439_, v___x_432_);
lean_dec_ref_known(v___x_439_, 3);
v___x_441_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_441_, 0, v_s_430_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
lean_ctor_set(v___x_441_, 2, v___x_431_);
v___x_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
return v___x_442_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0(lean_object* v_s_443_, lean_object* v_pat_444_){
_start:
{
lean_object* v___x_445_; 
v___x_445_ = l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg(v_s_443_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___boxed(lean_object* v_s_446_, lean_object* v_pat_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0(v_s_446_, v_pat_447_);
lean_dec_ref(v_pat_447_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f(lean_object* v_name_449_){
_start:
{
if (lean_obj_tag(v_name_449_) == 1)
{
lean_object* v_pre_450_; 
v_pre_450_ = lean_ctor_get(v_name_449_, 0);
if (lean_obj_tag(v_pre_450_) == 0)
{
lean_object* v_str_451_; lean_object* v___x_452_; 
v_str_451_ = lean_ctor_get(v_name_449_, 1);
lean_inc_ref(v_str_451_);
lean_dec_ref_known(v_name_449_, 2);
v___x_452_ = l_String_dropPrefix_x3f___at___00__private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f_spec__0___redArg(v_str_451_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v___x_453_; 
v___x_453_ = lean_box(0);
return v___x_453_;
}
else
{
lean_object* v_val_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_462_; 
v_val_454_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_462_ == 0)
{
v___x_456_ = v___x_452_;
v_isShared_457_ = v_isSharedCheck_462_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_val_454_);
lean_dec(v___x_452_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_462_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_458_; lean_object* v___x_460_; 
v___x_458_ = l_String_Slice_toString(v_val_454_);
lean_dec(v_val_454_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 0, v___x_458_);
v___x_460_ = v___x_456_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
else
{
lean_object* v___x_463_; 
lean_dec_ref_known(v_name_449_, 2);
v___x_463_ = lean_box(0);
return v___x_463_;
}
}
else
{
lean_object* v___x_464_; 
lean_dec(v_name_449_);
v___x_464_ = lean_box(0);
return v___x_464_;
}
}
}
lean_object* l_Lean_Server_documentUriFromModule_x3f(lean_object* v_modName_466_){
_start:
{
lean_object* v___x_468_; 
lean_inc(v_modName_466_);
v___x_468_ = l___private_Lean_Server_Utils_0__Lean_Server_externalNameToUri_x3f(v_modName_466_);
if (lean_obj_tag(v___x_468_) == 1)
{
lean_object* v___x_469_; 
lean_dec(v_modName_466_);
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
return v___x_469_;
}
else
{
lean_object* v___x_470_; 
lean_dec(v___x_468_);
v___x_470_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_470_) == 0)
{
lean_object* v_a_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v_a_471_ = lean_ctor_get(v___x_470_, 0);
lean_inc(v_a_471_);
lean_dec_ref_known(v___x_470_, 1);
v___x_472_ = ((lean_object*)(l_Lean_Server_documentUriFromModule_x3f___closed__0));
v___x_473_ = l_Lean_SearchPath_findModuleWithExt(v_a_471_, v___x_472_, v_modName_466_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_508_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_508_ == 0)
{
v___x_476_ = v___x_473_;
v_isShared_477_ = v_isSharedCheck_508_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_508_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
if (lean_obj_tag(v_a_474_) == 1)
{
lean_object* v_val_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_503_; 
lean_del_object(v___x_476_);
v_val_478_ = lean_ctor_get(v_a_474_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v_a_474_);
if (v_isSharedCheck_503_ == 0)
{
v___x_480_ = v_a_474_;
v_isShared_481_ = v_isSharedCheck_503_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_val_478_);
lean_dec(v_a_474_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_503_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_482_; 
v___x_482_ = lean_io_realpath(v_val_478_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_494_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_494_ == 0)
{
v___x_485_ = v___x_482_;
v_isShared_486_ = v_isSharedCheck_494_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_482_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_494_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_487_; lean_object* v___x_489_; 
v___x_487_ = l_System_Uri_pathToUri(v_a_483_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v___x_487_);
v___x_489_ = v___x_480_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v___x_487_);
v___x_489_ = v_reuseFailAlloc_493_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
lean_object* v___x_491_; 
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___x_489_);
v___x_491_ = v___x_485_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
else
{
lean_object* v_a_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_502_; 
lean_del_object(v___x_480_);
v_a_495_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_502_ == 0)
{
v___x_497_ = v___x_482_;
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_a_495_);
lean_dec(v___x_482_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_502_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_500_; 
if (v_isShared_498_ == 0)
{
v___x_500_ = v___x_497_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_495_);
v___x_500_ = v_reuseFailAlloc_501_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
return v___x_500_;
}
}
}
}
}
else
{
lean_object* v___x_504_; lean_object* v___x_506_; 
lean_dec(v_a_474_);
v___x_504_ = lean_box(0);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v___x_504_);
v___x_506_ = v___x_476_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
else
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
v_a_509_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_473_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_473_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
lean_dec(v_modName_466_);
v_a_517_ = lean_ctor_get(v___x_470_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_470_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_470_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_470_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_517_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_documentUriFromModule_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_modName_466_ = stack[0].m_obj;
lean_object* v_res_525_;
v_res_525_ = l_Lean_Server_documentUriFromModule_x3f(v_modName_466_);
stack->m_obj
 = v_res_525_;
}
LEAN_EXPORT lean_object* l_Lean_Server_documentUriFromModule_x3f___boxed(lean_object* v_modName_526_, lean_object* v_a_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_Server_documentUriFromModule_x3f(v_modName_526_);
return v_res_528_;
}
}
uint8_t l_instBEqOption_beq___at___00Lean_Server_moduleFromDocumentUri_spec__0(lean_object* v_x_529_, lean_object* v_x_530_){
_start:
{
if (lean_obj_tag(v_x_529_) == 0)
{
if (lean_obj_tag(v_x_530_) == 0)
{
uint8_t v___x_531_; 
v___x_531_ = 1;
return v___x_531_;
}
else
{
uint8_t v___x_532_; 
v___x_532_ = 0;
return v___x_532_;
}
}
else
{
if (lean_obj_tag(v_x_530_) == 0)
{
uint8_t v___x_533_; 
v___x_533_ = 0;
return v___x_533_;
}
else
{
lean_object* v_val_534_; lean_object* v_val_535_; uint8_t v___x_536_; 
v_val_534_ = lean_ctor_get(v_x_529_, 0);
v_val_535_ = lean_ctor_get(v_x_530_, 0);
v___x_536_ = lean_string_dec_eq(v_val_534_, v_val_535_);
return v___x_536_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Lean_Server_moduleFromDocumentUri_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_529_ = stack[0].m_obj;
lean_object* v_x_530_ = stack[1].m_obj;
uint8_t v_res_537_;
v_res_537_ = l_instBEqOption_beq___at___00Lean_Server_moduleFromDocumentUri_spec__0(v_x_529_, v_x_530_);
stack->m_num = v_res_537_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Server_moduleFromDocumentUri_spec__0___boxed(lean_object* v_x_538_, lean_object* v_x_539_){
_start:
{
uint8_t v_res_540_; lean_object* v_r_541_; 
v_res_540_ = l_instBEqOption_beq___at___00Lean_Server_moduleFromDocumentUri_spec__0(v_x_538_, v_x_539_);
lean_dec(v_x_539_);
lean_dec(v_x_538_);
v_r_541_ = lean_box(v_res_540_);
return v_r_541_;
}
}
lean_object* l_Lean_Server_moduleFromDocumentUri(lean_object* v_uri_544_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_System_Uri_fileUriToPath_x3f(v_uri_544_);
if (lean_obj_tag(v___x_546_) == 1)
{
lean_object* v_val_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_590_; 
v_val_547_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_590_ == 0)
{
v___x_549_ = v___x_546_;
v_isShared_550_ = v_isSharedCheck_590_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_val_547_);
lean_dec(v___x_546_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_590_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
lean_inc(v_val_547_);
v___x_551_ = l_System_FilePath_extension(v_val_547_);
v___x_552_ = ((lean_object*)(l_Lean_Server_moduleFromDocumentUri___closed__0));
v___x_553_ = l_instBEqOption_beq___at___00Lean_Server_moduleFromDocumentUri_spec__0(v___x_551_, v___x_552_);
lean_dec(v___x_551_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; lean_object* v___x_556_; 
lean_dec(v_val_547_);
v___x_554_ = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(v_uri_544_);
if (v_isShared_550_ == 0)
{
lean_ctor_set_tag(v___x_549_, 0);
lean_ctor_set(v___x_549_, 0, v___x_554_);
v___x_556_ = v___x_549_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
else
{
lean_object* v___x_558_; 
lean_del_object(v___x_549_);
v___x_558_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_560_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_a_559_);
lean_dec_ref_known(v___x_558_, 1);
v___x_560_ = l_Lean_searchModuleNameOfFileName(v_val_547_, v_a_559_);
lean_dec(v_a_559_);
if (lean_obj_tag(v___x_560_) == 0)
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_573_; 
v_a_561_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_573_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_573_ == 0)
{
v___x_563_ = v___x_560_;
v_isShared_564_ = v_isSharedCheck_573_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_560_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_573_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
if (lean_obj_tag(v_a_561_) == 1)
{
lean_object* v_val_565_; lean_object* v___x_567_; 
v_val_565_ = lean_ctor_get(v_a_561_, 0);
lean_inc(v_val_565_);
lean_dec_ref_known(v_a_561_, 1);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v_val_565_);
v___x_567_ = v___x_563_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_val_565_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
else
{
lean_object* v___x_569_; lean_object* v___x_571_; 
lean_dec(v_a_561_);
v___x_569_ = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(v_uri_544_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v___x_569_);
v___x_571_ = v___x_563_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
else
{
lean_object* v_a_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_581_; 
v_a_574_ = lean_ctor_get(v___x_560_, 0);
v_isSharedCheck_581_ = !lean_is_exclusive(v___x_560_);
if (v_isSharedCheck_581_ == 0)
{
v___x_576_ = v___x_560_;
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_a_574_);
lean_dec(v___x_560_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_581_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_579_; 
if (v_isShared_577_ == 0)
{
v___x_579_ = v___x_576_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_a_574_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
}
}
else
{
lean_object* v_a_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_589_; 
lean_dec(v_val_547_);
v_a_582_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_589_ == 0)
{
v___x_584_ = v___x_558_;
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_a_582_);
lean_dec(v___x_558_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_589_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_a_582_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
}
}
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; 
lean_dec(v___x_546_);
v___x_591_ = l___private_Lean_Server_Utils_0__Lean_Server_externalUriToName(v_uri_544_);
v___x_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_592_, 0, v___x_591_);
return v___x_592_;
}
}
}
LEAN_EXPORT void l_Lean_Server_moduleFromDocumentUri_0interp(lean_interpreter_value* stack)
{
lean_object* v_uri_544_ = stack[0].m_obj;
lean_object* v_res_593_;
v_res_593_ = l_Lean_Server_moduleFromDocumentUri(v_uri_544_);
stack->m_obj
 = v_res_593_;
}
LEAN_EXPORT lean_object* l_Lean_Server_moduleFromDocumentUri___boxed(lean_object* v_uri_594_, lean_object* v_a_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_Server_moduleFromDocumentUri(v_uri_594_);
lean_dec_ref(v_uri_594_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_Range_toLspRange(lean_object* v_text_597_, lean_object* v_r_598_){
_start:
{
lean_object* v_start_599_; lean_object* v_stop_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_609_; 
v_start_599_ = lean_ctor_get(v_r_598_, 0);
v_stop_600_ = lean_ctor_get(v_r_598_, 1);
v_isSharedCheck_609_ = !lean_is_exclusive(v_r_598_);
if (v_isSharedCheck_609_ == 0)
{
v___x_602_ = v_r_598_;
v_isShared_603_ = v_isSharedCheck_609_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_stop_600_);
lean_inc(v_start_599_);
lean_dec(v_r_598_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_609_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_607_; 
lean_inc_ref(v_text_597_);
v___x_604_ = l_Lean_FileMap_utf8PosToLspPos(v_text_597_, v_start_599_);
lean_dec(v_start_599_);
v___x_605_ = l_Lean_FileMap_utf8PosToLspPos(v_text_597_, v_stop_600_);
lean_dec(v_stop_600_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 1, v___x_605_);
lean_ctor_set(v___x_602_, 0, v___x_604_);
v___x_607_ = v___x_602_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_604_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v___x_605_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
lean_object* runtime_initialize_Init_System_Uri(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Lsp_Communication(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Lsp_Diagnostics(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Lsp_Extra(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_InfoTree_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_Utils(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_System_Uri(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Communication(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Diagnostics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Lsp_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_InfoTree_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_instInhabitedDocumentMeta_default = _init_l_Lean_Server_instInhabitedDocumentMeta_default();
lean_mark_persistent(l_Lean_Server_instInhabitedDocumentMeta_default);
l_Lean_Server_instInhabitedDocumentMeta = _init_l_Lean_Server_instInhabitedDocumentMeta();
lean_mark_persistent(l_Lean_Server_instInhabitedDocumentMeta);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_Utils(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_Uri(uint8_t builtin);
lean_object* initialize_Lean_Data_Lsp_Communication(uint8_t builtin);
lean_object* initialize_Lean_Data_Lsp_Diagnostics(uint8_t builtin);
lean_object* initialize_Lean_Data_Lsp_Extra(uint8_t builtin);
lean_object* initialize_Lean_Elab_InfoTree_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Utils(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_Uri(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Communication(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Diagnostics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_InfoTree_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Utils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_Utils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_Utils(builtin);
}
#ifdef __cplusplus
}
#endif
