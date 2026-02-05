// Lean compiler output
// Module: Lake.Util.Git
// Imports: public import Init.Data.ToString public import Lake.Util.Proc import Init.Data.String.TakeDrop import Init.Data.String.Search
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
static const lean_string_object l_Lake_Git_defaultRemote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "origin"};
static const lean_object* l_Lake_Git_defaultRemote___closed__0 = (const lean_object*)&l_Lake_Git_defaultRemote___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Git_defaultRemote = (const lean_object*)&l_Lake_Git_defaultRemote___closed__0_value;
static const lean_string_object l_Lake_Git_upstreamBranch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "master"};
static const lean_object* l_Lake_Git_upstreamBranch___closed__0 = (const lean_object*)&l_Lake_Git_upstreamBranch___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Git_upstreamBranch = (const lean_object*)&l_Lake_Git_upstreamBranch___closed__0_value;
static const lean_string_object l_Lake_Git_filterUrl_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = ".git"};
static const lean_object* l_Lake_Git_filterUrl_x3f___closed__0 = (const lean_object*)&l_Lake_Git_filterUrl_x3f___closed__0_value;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lake_Git_filterUrl_x3f___closed__1;
static const lean_string_object l_Lake_Git_filterUrl_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "git"};
static const lean_object* l_Lake_Git_filterUrl_x3f___closed__2 = (const lean_object*)&l_Lake_Git_filterUrl_x3f___closed__2_value;
static lean_object* l_Lake_Git_filterUrl_x3f___closed__3;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Git_filterUrl_x3f(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0_spec__0___redArg___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Git_isFullObjectName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Git_isFullObjectName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeFilePathGitRepo___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeFilePathGitRepo___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_instCoeFilePathGitRepo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instCoeFilePathGitRepo___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instCoeFilePathGitRepo___closed__0 = (const lean_object*)&l_Lake_instCoeFilePathGitRepo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instCoeFilePathGitRepo = (const lean_object*)&l_Lake_instCoeFilePathGitRepo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instToStringGitRepo = (const lean_object*)&l_Lake_instCoeFilePathGitRepo___closed__0_value;
static const lean_string_object l_Lake_GitRepo_cwd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_GitRepo_cwd___closed__0 = (const lean_object*)&l_Lake_GitRepo_cwd___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_GitRepo_cwd = (const lean_object*)&l_Lake_GitRepo_cwd___closed__0_value;
uint8_t l_System_FilePath_isDir(lean_object*);
LEAN_EXPORT uint8_t l_Lake_GitRepo_dirExists(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_dirExists___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lake_GitRepo_captureGit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_GitRepo_captureGit___closed__0 = (const lean_object*)&l_Lake_GitRepo_captureGit___closed__0_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_GitRepo_captureGit___closed__1;
lean_object* l_Lake_captureProc_x27(lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_captureProc_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_testProc(lean_object*);
LEAN_EXPORT uint8_t l_Lake_GitRepo_testGit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_testGit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_clone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "clone"};
static const lean_object* l_Lake_GitRepo_clone___closed__0 = (const lean_object*)&l_Lake_GitRepo_clone___closed__0_value;
static lean_object* l_Lake_GitRepo_clone___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_GitRepo_clone___closed__2;
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_quietInit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "init"};
static const lean_object* l_Lake_GitRepo_quietInit___closed__0 = (const lean_object*)&l_Lake_GitRepo_quietInit___closed__0_value;
static const lean_string_object l_Lake_GitRepo_quietInit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-q"};
static const lean_object* l_Lake_GitRepo_quietInit___closed__1 = (const lean_object*)&l_Lake_GitRepo_quietInit___closed__1_value;
static lean_object* l_Lake_GitRepo_quietInit___closed__2;
static lean_object* l_Lake_GitRepo_quietInit___closed__3;
static lean_object* l_Lake_GitRepo_quietInit___closed__4;
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_insideWorkTree___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rev-parse"};
static const lean_object* l_Lake_GitRepo_insideWorkTree___closed__0 = (const lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__0_value;
static const lean_string_object l_Lake_GitRepo_insideWorkTree___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "--is-inside-work-tree"};
static const lean_object* l_Lake_GitRepo_insideWorkTree___closed__1 = (const lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__1_value;
static lean_object* l_Lake_GitRepo_insideWorkTree___closed__2;
static lean_object* l_Lake_GitRepo_insideWorkTree___closed__3;
LEAN_EXPORT uint8_t l_Lake_GitRepo_insideWorkTree(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_insideWorkTree___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_fetch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "fetch"};
static const lean_object* l_Lake_GitRepo_fetch___closed__0 = (const lean_object*)&l_Lake_GitRepo_fetch___closed__0_value;
static const lean_string_object l_Lake_GitRepo_fetch___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "--tags"};
static const lean_object* l_Lake_GitRepo_fetch___closed__1 = (const lean_object*)&l_Lake_GitRepo_fetch___closed__1_value;
static const lean_string_object l_Lake_GitRepo_fetch___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "--force"};
static const lean_object* l_Lake_GitRepo_fetch___closed__2 = (const lean_object*)&l_Lake_GitRepo_fetch___closed__2_value;
static lean_object* l_Lake_GitRepo_fetch___closed__3;
static lean_object* l_Lake_GitRepo_fetch___closed__4;
static lean_object* l_Lake_GitRepo_fetch___closed__5;
static lean_object* l_Lake_GitRepo_fetch___closed__6;
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_checkoutBranch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "checkout"};
static const lean_object* l_Lake_GitRepo_checkoutBranch___closed__0 = (const lean_object*)&l_Lake_GitRepo_checkoutBranch___closed__0_value;
static const lean_string_object l_Lake_GitRepo_checkoutBranch___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-B"};
static const lean_object* l_Lake_GitRepo_checkoutBranch___closed__1 = (const lean_object*)&l_Lake_GitRepo_checkoutBranch___closed__1_value;
static lean_object* l_Lake_GitRepo_checkoutBranch___closed__2;
static lean_object* l_Lake_GitRepo_checkoutBranch___closed__3;
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_checkoutDetach___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "--detach"};
static const lean_object* l_Lake_GitRepo_checkoutDetach___closed__0 = (const lean_object*)&l_Lake_GitRepo_checkoutDetach___closed__0_value;
static const lean_string_object l_Lake_GitRepo_checkoutDetach___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "--"};
static const lean_object* l_Lake_GitRepo_checkoutDetach___closed__1 = (const lean_object*)&l_Lake_GitRepo_checkoutDetach___closed__1_value;
static lean_object* l_Lake_GitRepo_checkoutDetach___closed__2;
static lean_object* l_Lake_GitRepo_checkoutDetach___closed__3;
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_resolveRevision_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "--verify"};
static const lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_resolveRevision_x3f___closed__0_value;
static const lean_string_object l_Lake_GitRepo_resolveRevision_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "--end-of-options"};
static const lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__1 = (const lean_object*)&l_Lake_GitRepo_resolveRevision_x3f___closed__1_value;
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__2;
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__3;
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_resolveRevision___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = ": revision not found '"};
static const lean_object* l_Lake_GitRepo_resolveRevision___closed__0 = (const lean_object*)&l_Lake_GitRepo_resolveRevision___closed__0_value;
static const lean_string_object l_Lake_GitRepo_resolveRevision___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lake_GitRepo_resolveRevision___closed__1 = (const lean_object*)&l_Lake_GitRepo_resolveRevision___closed__1_value;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getHeadRevision_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l_Lake_GitRepo_getHeadRevision_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_getHeadRevision_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getHeadRevision___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 114, .m_capacity = 114, .m_length = 113, .m_data = ": could not resolve 'HEAD' to a commit; the repository may be corrupt, so you may need to remove it and try again"};
static const lean_object* l_Lake_GitRepo_getHeadRevision___closed__0 = (const lean_object*)&l_Lake_GitRepo_getHeadRevision___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_split___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_split___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0 = (const lean_object*)&l_String_Slice_split___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_split___at___00Lake_GitRepo_getHeadRevisions_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_split___at___00Lake_GitRepo_getHeadRevisions_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_toStringArray___at___00Lake_GitRepo_getHeadRevisions_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Iter_toStringArray___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_Iter_toStringArray___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getHeadRevisions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rev-list"};
static const lean_object* l_Lake_GitRepo_getHeadRevisions___closed__0 = (const lean_object*)&l_Lake_GitRepo_getHeadRevisions___closed__0_value;
static lean_object* l_Lake_GitRepo_getHeadRevisions___closed__1;
static lean_object* l_Lake_GitRepo_getHeadRevisions___closed__2;
static const lean_string_object l_Lake_GitRepo_getHeadRevisions___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-n"};
static const lean_object* l_Lake_GitRepo_getHeadRevisions___closed__3 = (const lean_object*)&l_Lake_GitRepo_getHeadRevisions___closed__3_value;
static lean_object* l_Lake_GitRepo_getHeadRevisions___closed__4;
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iter_toStringArray___at___00Lake_GitRepo_getHeadRevisions_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_toStringArray___at___00Lake_GitRepo_getHeadRevisions_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_resolveRemoteRevision___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Lake_GitRepo_resolveRemoteRevision___closed__0 = (const lean_object*)&l_Lake_GitRepo_resolveRemoteRevision___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_branchExists___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "show-ref"};
static const lean_object* l_Lake_GitRepo_branchExists___closed__0 = (const lean_object*)&l_Lake_GitRepo_branchExists___closed__0_value;
static const lean_string_object l_Lake_GitRepo_branchExists___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "refs/heads/"};
static const lean_object* l_Lake_GitRepo_branchExists___closed__1 = (const lean_object*)&l_Lake_GitRepo_branchExists___closed__1_value;
static lean_object* l_Lake_GitRepo_branchExists___closed__2;
static lean_object* l_Lake_GitRepo_branchExists___closed__3;
LEAN_EXPORT uint8_t l_Lake_GitRepo_branchExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_branchExists___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_revisionExists___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "^{commit}"};
static const lean_object* l_Lake_GitRepo_revisionExists___closed__0 = (const lean_object*)&l_Lake_GitRepo_revisionExists___closed__0_value;
static lean_object* l_Lake_GitRepo_revisionExists___closed__1;
static lean_object* l_Lake_GitRepo_revisionExists___closed__2;
LEAN_EXPORT uint8_t l_Lake_GitRepo_revisionExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_revisionExists___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getTags_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getTags___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "tag"};
static const lean_object* l_Lake_GitRepo_getTags___closed__0 = (const lean_object*)&l_Lake_GitRepo_getTags___closed__0_value;
static lean_object* l_Lake_GitRepo_getTags___closed__1;
static lean_object* l_Lake_GitRepo_getTags___closed__2;
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getTags_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_findTag_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "describe"};
static const lean_object* l_Lake_GitRepo_findTag_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_findTag_x3f___closed__0_value;
static const lean_string_object l_Lake_GitRepo_findTag_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "--exact-match"};
static const lean_object* l_Lake_GitRepo_findTag_x3f___closed__1 = (const lean_object*)&l_Lake_GitRepo_findTag_x3f___closed__1_value;
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__2;
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__3;
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getRemoteUrl_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "remote"};
static const lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_getRemoteUrl_x3f___closed__0_value;
static const lean_string_object l_Lake_GitRepo_getRemoteUrl_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "get-url"};
static const lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__1 = (const lean_object*)&l_Lake_GitRepo_getRemoteUrl_x3f___closed__1_value;
static lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__2;
static lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_hasNoDiff___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "diff"};
static const lean_object* l_Lake_GitRepo_hasNoDiff___closed__0 = (const lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__0_value;
static const lean_string_object l_Lake_GitRepo_hasNoDiff___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "--exit-code"};
static const lean_object* l_Lake_GitRepo_hasNoDiff___closed__1 = (const lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__1_value;
static lean_object* l_Lake_GitRepo_hasNoDiff___closed__2;
static lean_object* l_Lake_GitRepo_hasNoDiff___closed__3;
static lean_object* l_Lake_GitRepo_hasNoDiff___closed__4;
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasNoDiff(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasNoDiff___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasDiff(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasDiff___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Lake_Git_filterUrl_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__0));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Git_filterUrl_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Git_filterUrl_x3f(lean_object* x_1) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
x_18 = lean_string_utf8_byte_size(x_1);
x_19 = l_Lake_Git_filterUrl_x3f___closed__3;
x_20 = lean_nat_dec_le(x_19, x_18);
if (x_20 == 0)
{
goto block_16;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_string_memcmp(x_1, x_17, x_21, x_21, x_19);
if (x_22 == 0)
{
goto block_16;
}
else
{
lean_object* x_23; 
lean_dec_ref(x_1);
x_23 = lean_box(0);
return x_23;
}
}
block_16:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__0));
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = l_Lake_Git_filterUrl_x3f___closed__1;
x_5 = lean_nat_dec_le(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_sub(x_3, x_4);
x_9 = lean_string_memcmp(x_1, x_2, x_8, x_7, x_4);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_unsigned_to_nat(4u);
lean_inc_ref(x_1);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_3);
x_13 = l_String_Slice_Pos_prevn(x_12, x_3, x_11);
lean_dec_ref(x_12);
x_14 = lean_string_utf8_extract(x_1, x_7, x_13);
lean_dec(x_13);
lean_dec_ref(x_1);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_nat_sub(x_6, x_5);
x_8 = lean_nat_dec_eq(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_15; uint32_t x_19; uint8_t x_20; uint32_t x_26; uint8_t x_27; 
x_9 = lean_nat_add(x_5, x_2);
x_10 = lean_string_utf8_next_fast(x_4, x_9);
x_11 = lean_nat_sub(x_10, x_5);
x_19 = lean_string_utf8_get_fast(x_4, x_9);
lean_dec(x_9);
x_26 = 48;
x_27 = lean_uint32_dec_le(x_26, x_19);
if (x_27 == 0)
{
x_20 = x_27;
goto block_25;
}
else
{
uint32_t x_28; uint8_t x_29; 
x_28 = 57;
x_29 = lean_uint32_dec_le(x_19, x_28);
x_20 = x_29;
goto block_25;
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
block_18:
{
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_11);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
goto block_14;
}
}
block_25:
{
if (x_20 == 0)
{
uint32_t x_21; uint8_t x_22; 
x_21 = 97;
x_22 = lean_uint32_dec_le(x_21, x_19);
if (x_22 == 0)
{
x_15 = x_22;
goto block_18;
}
else
{
uint32_t x_23; uint8_t x_24; 
x_23 = 102;
x_24 = lean_uint32_dec_le(x_19, x_23);
x_15 = x_24;
goto block_18;
}
}
else
{
goto block_14;
}
}
}
else
{
lean_dec(x_2);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0_spec__0_spec__1___redArg(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 1)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec_ref(x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_free_object(x_4);
lean_dec(x_6);
return x_3;
}
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_dec(x_8);
return x_3;
}
}
}
else
{
lean_dec(x_4);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0_spec__0___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0_spec__0___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_nat_add(x_4, x_2);
lean_inc(x_5);
lean_inc_ref(x_3);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_5);
x_8 = l_String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0_spec__0___redArg(x_7);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_9);
x_11 = lean_nat_dec_lt(x_2, x_10);
lean_dec(x_2);
if (x_11 == 0)
{
lean_dec(x_10);
return x_7;
}
else
{
lean_dec_ref(x_7);
x_2 = x_10;
goto _start;
}
}
else
{
lean_dec(x_8);
lean_dec(x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_Git_isFullObjectName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_string_length(x_1);
x_3 = lean_unsigned_to_nat(40u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_string_utf8_byte_size(x_1);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0(x_7, x_5);
lean_dec_ref(x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 2);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_nat_sub(x_10, x_9);
lean_dec(x_9);
lean_dec(x_10);
x_12 = lean_nat_dec_eq(x_11, x_5);
lean_dec(x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Git_isFullObjectName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_Git_isFullObjectName(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0_spec__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0_spec__0_spec__1___redArg(x_1, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00Lake_Git_isFullObjectName_spec__0_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeFilePathGitRepo___lam__0(lean_object* x_1) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeFilePathGitRepo___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instCoeFilePathGitRepo___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_dirExists(lean_object* x_1) {
_start:
{
uint8_t x_3; 
x_3 = l_System_FilePath_isDir(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_dirExists___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_GitRepo_dirExists(x_1);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_GitRepo_captureGit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_5 = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
x_6 = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lake_GitRepo_captureGit___closed__1;
x_10 = 1;
x_11 = 0;
x_12 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_6);
lean_ctor_set(x_12, 2, x_1);
lean_ctor_set(x_12, 3, x_7);
lean_ctor_set(x_12, 4, x_9);
lean_ctor_set_uint8(x_12, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*5 + 1, x_11);
x_13 = l_Lake_captureProc_x27(x_12, x_3);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_16);
lean_dec(x_15);
x_17 = lean_string_utf8_byte_size(x_16);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_8);
lean_ctor_set(x_18, 2, x_17);
x_19 = l_String_Slice_trimAscii(x_18);
lean_dec_ref(x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 2);
lean_inc(x_22);
lean_dec_ref(x_19);
x_23 = lean_string_utf8_extract(x_20, x_21, x_22);
lean_dec(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_ctor_set(x_13, 0, x_23);
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_26);
lean_dec(x_24);
x_27 = lean_string_utf8_byte_size(x_26);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_8);
lean_ctor_set(x_28, 2, x_27);
x_29 = l_String_Slice_trimAscii(x_28);
lean_dec_ref(x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc_ref(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 2);
lean_inc(x_32);
lean_dec_ref(x_29);
x_33 = lean_string_utf8_extract(x_30, x_31, x_32);
lean_dec(x_32);
lean_dec(x_31);
lean_dec_ref(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_25);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_13);
if (x_35 == 0)
{
return x_13;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_13, 0);
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_13);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_GitRepo_captureGit(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
x_5 = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = l_Lake_GitRepo_captureGit___closed__1;
x_8 = 1;
x_9 = 0;
x_10 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_1);
lean_ctor_set(x_10, 3, x_6);
lean_ctor_set(x_10, 4, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*5 + 1, x_9);
x_11 = l_Lake_captureProc_x3f(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_GitRepo_captureGit_x3f(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_5 = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
x_6 = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_8 = l_Lake_GitRepo_captureGit___closed__1;
x_9 = 1;
x_10 = 0;
x_11 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_1);
lean_ctor_set(x_11, 3, x_7);
lean_ctor_set(x_11, 4, x_8);
lean_ctor_set_uint8(x_11, sizeof(void*)*5, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*5 + 1, x_10);
x_12 = l_Lake_proc(x_11, x_9, x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_GitRepo_execGit(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_testGit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; 
x_4 = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
x_5 = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = l_Lake_GitRepo_captureGit___closed__1;
x_8 = 1;
x_9 = 0;
x_10 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_1);
lean_ctor_set(x_10, 3, x_6);
lean_ctor_set(x_10, 4, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*5 + 1, x_9);
x_11 = l_Lake_testProc(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_testGit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lake_GitRepo_testGit(x_1, x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_GitRepo_clone___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_GitRepo_clone___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_clone___closed__0));
x_2 = l_Lake_GitRepo_clone___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_5 = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
x_6 = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
x_7 = l_Lake_GitRepo_clone___closed__2;
x_8 = lean_array_push(x_7, x_1);
x_9 = lean_array_push(x_8, x_2);
x_10 = lean_box(0);
x_11 = l_Lake_GitRepo_captureGit___closed__1;
x_12 = 1;
x_13 = 0;
x_14 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_6);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*5, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*5 + 1, x_13);
x_15 = l_Lake_proc(x_14, x_12, x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_GitRepo_clone(x_1, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lake_GitRepo_quietInit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_GitRepo_quietInit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_quietInit___closed__0));
x_2 = l_Lake_GitRepo_quietInit___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_quietInit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_quietInit___closed__1));
x_2 = l_Lake_GitRepo_quietInit___closed__3;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_4 = l_Lake_GitRepo_quietInit___closed__4;
x_5 = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
x_6 = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = l_Lake_GitRepo_captureGit___closed__1;
x_9 = 1;
x_10 = 0;
x_11 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_4);
lean_ctor_set(x_11, 3, x_7);
lean_ctor_set(x_11, 4, x_8);
lean_ctor_set_uint8(x_11, sizeof(void*)*5, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*5 + 1, x_10);
x_12 = l_Lake_proc(x_11, x_9, x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_GitRepo_quietInit(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_GitRepo_insideWorkTree___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_insideWorkTree___closed__0));
x_2 = l_Lake_GitRepo_quietInit___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_insideWorkTree___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_insideWorkTree___closed__1));
x_2 = l_Lake_GitRepo_insideWorkTree___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_insideWorkTree(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; 
x_3 = l_Lake_GitRepo_insideWorkTree___closed__3;
x_4 = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
x_5 = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = l_Lake_GitRepo_captureGit___closed__1;
x_8 = 1;
x_9 = 0;
x_10 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_3);
lean_ctor_set(x_10, 3, x_6);
lean_ctor_set(x_10, 4, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*5 + 1, x_9);
x_11 = l_Lake_testProc(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_insideWorkTree___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_GitRepo_insideWorkTree(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_fetch___closed__0));
x_2 = l_Lake_GitRepo_fetch___closed__3;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_fetch___closed__1));
x_2 = l_Lake_GitRepo_fetch___closed__4;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_fetch___closed__2));
x_2 = l_Lake_GitRepo_fetch___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_5 = l_Lake_GitRepo_fetch___closed__6;
x_6 = lean_array_push(x_5, x_2);
x_7 = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
x_8 = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = l_Lake_GitRepo_captureGit___closed__1;
x_11 = 1;
x_12 = 0;
x_13 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_6);
lean_ctor_set(x_13, 3, x_9);
lean_ctor_set(x_13, 4, x_10);
lean_ctor_set_uint8(x_13, sizeof(void*)*5, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*5 + 1, x_12);
x_14 = l_Lake_proc(x_13, x_11, x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_GitRepo_fetch(x_1, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutBranch___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_checkoutBranch___closed__0));
x_2 = l_Lake_GitRepo_clone___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutBranch___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_checkoutBranch___closed__1));
x_2 = l_Lake_GitRepo_checkoutBranch___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_5 = l_Lake_GitRepo_checkoutBranch___closed__3;
x_6 = lean_array_push(x_5, x_1);
x_7 = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
x_8 = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_2);
x_10 = l_Lake_GitRepo_captureGit___closed__1;
x_11 = 1;
x_12 = 0;
x_13 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_6);
lean_ctor_set(x_13, 3, x_9);
lean_ctor_set(x_13, 4, x_10);
lean_ctor_set_uint8(x_13, sizeof(void*)*5, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*5 + 1, x_12);
x_14 = l_Lake_proc(x_13, x_11, x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_GitRepo_checkoutBranch(x_1, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutDetach___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_checkoutBranch___closed__0));
x_2 = l_Lake_GitRepo_fetch___closed__3;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutDetach___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_checkoutDetach___closed__0));
x_2 = l_Lake_GitRepo_checkoutDetach___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_5 = ((lean_object*)(l_Lake_GitRepo_checkoutDetach___closed__1));
x_6 = l_Lake_GitRepo_checkoutDetach___closed__3;
x_7 = lean_array_push(x_6, x_1);
x_8 = lean_array_push(x_7, x_5);
x_9 = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
x_10 = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_2);
x_12 = l_Lake_GitRepo_captureGit___closed__1;
x_13 = 1;
x_14 = 0;
x_15 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_8);
lean_ctor_set(x_15, 3, x_11);
lean_ctor_set(x_15, 4, x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*5, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*5 + 1, x_14);
x_16 = l_Lake_proc(x_15, x_13, x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_GitRepo_checkoutDetach(x_1, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_insideWorkTree___closed__0));
x_2 = l_Lake_GitRepo_fetch___closed__3;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__0));
x_2 = l_Lake_GitRepo_resolveRevision_x3f___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__1));
x_2 = l_Lake_GitRepo_resolveRevision_x3f___closed__3;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_4 = l_Lake_GitRepo_resolveRevision_x3f___closed__4;
x_5 = lean_array_push(x_4, x_1);
x_6 = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
x_7 = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = l_Lake_GitRepo_captureGit___closed__1;
x_10 = 1;
x_11 = 0;
x_12 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_5);
lean_ctor_set(x_12, 3, x_8);
lean_ctor_set(x_12, 4, x_9);
lean_ctor_set_uint8(x_12, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*5 + 1, x_11);
x_13 = l_Lake_captureProc_x3f(x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_GitRepo_resolveRevision_x3f(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; 
lean_inc_ref(x_1);
x_5 = l_Lake_Git_isFullObjectName(x_1);
if (x_5 == 0)
{
lean_object* x_6; 
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_6 = l_Lake_GitRepo_resolveRevision_x3f(x_1, x_2);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_9 = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__0));
x_10 = lean_string_append(x_2, x_9);
x_11 = lean_string_append(x_10, x_1);
lean_dec_ref(x_1);
x_12 = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__1));
x_13 = lean_string_append(x_11, x_12);
x_14 = 3;
x_15 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
x_16 = lean_array_get_size(x_3);
x_17 = lean_array_push(x_3, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; 
lean_dec_ref(x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_GitRepo_resolveRevision(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = ((lean_object*)(l_Lake_GitRepo_getHeadRevision_x3f___closed__0));
x_4 = l_Lake_GitRepo_resolveRevision_x3f(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_GitRepo_getHeadRevision_x3f(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = ((lean_object*)(l_Lake_GitRepo_getHeadRevision_x3f___closed__0));
lean_inc_ref(x_1);
x_5 = l_Lake_GitRepo_resolveRevision_x3f(x_4, x_1);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_8 = ((lean_object*)(l_Lake_GitRepo_getHeadRevision___closed__0));
x_9 = lean_string_append(x_1, x_8);
x_10 = 3;
x_11 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
x_12 = lean_array_get_size(x_2);
x_13 = lean_array_push(x_2, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_GitRepo_getHeadRevision(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___at___00Lake_GitRepo_getHeadRevisions_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = ((lean_object*)(l_String_Slice_split___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___at___00Lake_GitRepo_getHeadRevisions_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_split___at___00Lake_GitRepo_getHeadRevisions_spec__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_toStringArray___at___00Lake_GitRepo_getHeadRevisions_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = lean_ctor_get(x_1, 2);
x_18 = lean_nat_sub(x_17, x_16);
x_19 = lean_nat_dec_eq(x_14, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
uint32_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint32_t x_24; uint8_t x_25; 
x_20 = 10;
x_21 = lean_nat_add(x_16, x_14);
x_22 = lean_string_utf8_next_fast(x_15, x_21);
x_23 = lean_nat_sub(x_22, x_16);
x_24 = lean_string_utf8_get_fast(x_15, x_21);
lean_dec(x_21);
x_25 = lean_uint32_dec_eq(x_24, x_20);
if (x_25 == 0)
{
lean_dec(x_14);
lean_ctor_set(x_2, 1, x_23);
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_inc_ref(x_1);
x_27 = l_String_Slice_slice_x21(x_1, x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
lean_inc(x_23);
lean_ctor_set(x_2, 1, x_23);
lean_ctor_set(x_2, 0, x_23);
x_28 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 2);
lean_inc(x_30);
lean_dec_ref(x_27);
x_4 = x_2;
x_5 = x_28;
x_6 = x_29;
x_7 = x_30;
goto block_11;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_free_object(x_2);
lean_dec(x_14);
x_31 = lean_nat_add(x_16, x_13);
lean_dec(x_13);
x_32 = lean_box(1);
lean_inc(x_17);
lean_inc_ref(x_15);
x_4 = x_32;
x_5 = x_15;
x_6 = x_31;
x_7 = x_17;
goto block_11;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_33 = lean_ctor_get(x_2, 0);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_2);
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_1, 2);
x_38 = lean_nat_sub(x_37, x_36);
x_39 = lean_nat_dec_eq(x_34, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
uint32_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint32_t x_44; uint8_t x_45; 
x_40 = 10;
x_41 = lean_nat_add(x_36, x_34);
x_42 = lean_string_utf8_next_fast(x_35, x_41);
x_43 = lean_nat_sub(x_42, x_36);
x_44 = lean_string_utf8_get_fast(x_35, x_41);
lean_dec(x_41);
x_45 = lean_uint32_dec_eq(x_44, x_40);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_34);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_33);
lean_ctor_set(x_46, 1, x_43);
x_2 = x_46;
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_inc_ref(x_1);
x_48 = l_String_Slice_slice_x21(x_1, x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
lean_inc(x_43);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_43);
x_50 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_48, 2);
lean_inc(x_52);
lean_dec_ref(x_48);
x_4 = x_49;
x_5 = x_50;
x_6 = x_51;
x_7 = x_52;
goto block_11;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_34);
x_53 = lean_nat_add(x_36, x_33);
lean_dec(x_33);
x_54 = lean_box(1);
lean_inc(x_37);
lean_inc_ref(x_35);
x_4 = x_54;
x_5 = x_35;
x_6 = x_53;
x_7 = x_37;
goto block_11;
}
}
}
else
{
lean_dec_ref(x_1);
return x_3;
}
block_11:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_string_utf8_extract(x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_9 = lean_array_push(x_3, x_8);
x_2 = x_4;
x_3 = x_9;
goto _start;
}
}
}
static lean_object* _init_l_Std_Iter_toStringArray___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toStringArray___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Std_Iter_toStringArray___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg___closed__0;
x_4 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_toStringArray___at___00Lake_GitRepo_getHeadRevisions_spec__1_spec__1___redArg(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_GitRepo_getHeadRevisions___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_getHeadRevisions___closed__0));
x_2 = l_Lake_GitRepo_quietInit___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_getHeadRevisions___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_getHeadRevision_x3f___closed__0));
x_2 = l_Lake_GitRepo_getHeadRevisions___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_getHeadRevisions___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_getHeadRevisions___closed__3));
x_2 = l_Lake_GitRepo_quietInit___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = l_Lake_GitRepo_getHeadRevisions___closed__2;
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_nat_dec_eq(x_2, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = l_Nat_reprFast(x_2);
x_62 = l_Lake_GitRepo_getHeadRevisions___closed__4;
x_63 = lean_array_push(x_62, x_61);
x_64 = l_Array_append___redArg(x_58, x_63);
lean_dec_ref(x_63);
x_5 = x_64;
goto block_57;
}
else
{
lean_dec(x_2);
x_5 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_6 = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
x_7 = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lake_GitRepo_captureGit___closed__1;
x_11 = 1;
x_12 = 0;
x_13 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set(x_13, 2, x_5);
lean_ctor_set(x_13, 3, x_8);
lean_ctor_set(x_13, 4, x_10);
lean_ctor_set_uint8(x_13, sizeof(void*)*5, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*5 + 1, x_12);
x_14 = l_Lake_captureProc_x27(x_13, x_3);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_17);
lean_dec(x_16);
x_18 = lean_string_utf8_byte_size(x_17);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_9);
lean_ctor_set(x_19, 2, x_18);
x_20 = l_String_Slice_trimAscii(x_19);
lean_dec_ref(x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_ctor_get(x_20, 2);
x_25 = lean_string_utf8_extract(x_22, x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
x_26 = lean_string_utf8_byte_size(x_25);
lean_ctor_set(x_20, 2, x_26);
lean_ctor_set(x_20, 1, x_9);
lean_ctor_set(x_20, 0, x_25);
x_27 = l_String_Slice_split___at___00Lake_GitRepo_getHeadRevisions_spec__0(x_20);
x_28 = l_Std_Iter_toStringArray___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(x_20, x_27);
lean_ctor_set(x_14, 0, x_28);
return x_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
x_31 = lean_ctor_get(x_20, 2);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_32 = lean_string_utf8_extract(x_29, x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
x_33 = lean_string_utf8_byte_size(x_32);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_9);
lean_ctor_set(x_34, 2, x_33);
x_35 = l_String_Slice_split___at___00Lake_GitRepo_getHeadRevisions_spec__0(x_34);
x_36 = l_Std_Iter_toStringArray___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(x_34, x_35);
lean_ctor_set(x_14, 0, x_36);
return x_14;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_37 = lean_ctor_get(x_14, 0);
x_38 = lean_ctor_get(x_14, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_14);
x_39 = lean_ctor_get(x_37, 0);
lean_inc_ref(x_39);
lean_dec(x_37);
x_40 = lean_string_utf8_byte_size(x_39);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_9);
lean_ctor_set(x_41, 2, x_40);
x_42 = l_String_Slice_trimAscii(x_41);
lean_dec_ref(x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc_ref(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 2);
lean_inc(x_45);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 x_46 = x_42;
} else {
 lean_dec_ref(x_42);
 x_46 = lean_box(0);
}
x_47 = lean_string_utf8_extract(x_43, x_44, x_45);
lean_dec(x_45);
lean_dec(x_44);
lean_dec_ref(x_43);
x_48 = lean_string_utf8_byte_size(x_47);
if (lean_is_scalar(x_46)) {
 x_49 = lean_alloc_ctor(0, 3, 0);
} else {
 x_49 = x_46;
}
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_9);
lean_ctor_set(x_49, 2, x_48);
x_50 = l_String_Slice_split___at___00Lake_GitRepo_getHeadRevisions_spec__0(x_49);
x_51 = l_Std_Iter_toStringArray___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(x_49, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_38);
return x_52;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_14);
if (x_53 == 0)
{
return x_14;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_14, 0);
x_55 = lean_ctor_get(x_14, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_14);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_GitRepo_getHeadRevisions(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Iter_toStringArray___at___00Lake_GitRepo_getHeadRevisions_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Iter_toStringArray___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_toStringArray___at___00Lake_GitRepo_getHeadRevisions_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Std_Iter_toStringArray___at___00Lake_GitRepo_getHeadRevisions_spec__1_spec__1___redArg(x_1, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
lean_inc_ref(x_1);
x_6 = l_Lake_Git_isFullObjectName(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = ((lean_object*)(l_Lake_GitRepo_resolveRemoteRevision___closed__0));
x_8 = lean_string_append(x_2, x_7);
x_9 = lean_string_append(x_8, x_1);
lean_inc_ref(x_3);
x_10 = l_Lake_GitRepo_resolveRevision_x3f(x_9, x_3);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; lean_object* x_12; 
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_10);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_13 = l_Lake_GitRepo_resolveRevision_x3f(x_1, x_3);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_13);
x_16 = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__0));
x_17 = lean_string_append(x_3, x_16);
x_18 = lean_string_append(x_17, x_1);
lean_dec_ref(x_1);
x_19 = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__1));
x_20 = lean_string_append(x_18, x_19);
x_21 = 3;
x_22 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_21);
x_23 = lean_array_get_size(x_4);
x_24 = lean_array_push(x_4, x_22);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_4);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_GitRepo_resolveRemoteRevision(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_6 = l_Lake_GitRepo_fetch(x_1, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = ((lean_object*)(l_Lake_Git_upstreamBranch___closed__0));
x_9 = l_Lake_GitRepo_resolveRemoteRevision(x_8, x_3, x_1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec_ref(x_6);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec_ref(x_2);
x_12 = l_Lake_GitRepo_resolveRemoteRevision(x_11, x_3, x_1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_GitRepo_findRemoteRevision(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lake_GitRepo_branchExists___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_branchExists___closed__0));
x_2 = l_Lake_GitRepo_clone___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_branchExists___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__0));
x_2 = l_Lake_GitRepo_branchExists___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_branchExists(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; 
x_4 = ((lean_object*)(l_Lake_GitRepo_branchExists___closed__1));
x_5 = lean_string_append(x_4, x_1);
x_6 = l_Lake_GitRepo_branchExists___closed__3;
x_7 = lean_array_push(x_6, x_5);
x_8 = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
x_9 = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_2);
x_11 = l_Lake_GitRepo_captureGit___closed__1;
x_12 = 1;
x_13 = 0;
x_14 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_7);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*5, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*5 + 1, x_13);
x_15 = l_Lake_testProc(x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_branchExists___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lake_GitRepo_branchExists(x_1, x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_GitRepo_revisionExists___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_insideWorkTree___closed__0));
x_2 = l_Lake_GitRepo_clone___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_revisionExists___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__0));
x_2 = l_Lake_GitRepo_revisionExists___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_revisionExists(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; 
x_4 = ((lean_object*)(l_Lake_GitRepo_revisionExists___closed__0));
x_5 = lean_string_append(x_1, x_4);
x_6 = l_Lake_GitRepo_revisionExists___closed__2;
x_7 = lean_array_push(x_6, x_5);
x_8 = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
x_9 = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_2);
x_11 = l_Lake_GitRepo_captureGit___closed__1;
x_12 = 1;
x_13 = 0;
x_14 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_7);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*5, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*5 + 1, x_13);
x_15 = l_Lake_testProc(x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_revisionExists___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lake_GitRepo_revisionExists(x_1, x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getTags_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_nat_sub(x_18, x_17);
x_20 = lean_nat_dec_eq(x_16, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
uint32_t x_21; lean_object* x_22; uint32_t x_23; uint8_t x_24; 
x_21 = 10;
x_22 = lean_string_utf8_next_fast(x_2, x_16);
x_23 = lean_string_utf8_get_fast(x_2, x_16);
x_24 = lean_uint32_dec_eq(x_23, x_21);
if (x_24 == 0)
{
lean_dec(x_16);
lean_ctor_set(x_4, 1, x_22);
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc_ref(x_1);
x_26 = l_String_Slice_slice_x21(x_1, x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
lean_ctor_set(x_4, 1, x_22);
lean_ctor_set(x_4, 0, x_22);
x_27 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 2);
lean_inc(x_29);
lean_dec_ref(x_26);
x_6 = x_4;
x_7 = x_27;
x_8 = x_28;
x_9 = x_29;
goto block_13;
}
}
else
{
lean_object* x_30; 
lean_free_object(x_4);
lean_dec(x_16);
x_30 = lean_box(1);
lean_inc(x_3);
lean_inc_ref(x_2);
x_6 = x_30;
x_7 = x_2;
x_8 = x_15;
x_9 = x_3;
goto block_13;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_ctor_get(x_4, 0);
x_32 = lean_ctor_get(x_4, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_4);
x_33 = lean_ctor_get(x_1, 1);
x_34 = lean_ctor_get(x_1, 2);
x_35 = lean_nat_sub(x_34, x_33);
x_36 = lean_nat_dec_eq(x_32, x_35);
lean_dec(x_35);
if (x_36 == 0)
{
uint32_t x_37; lean_object* x_38; uint32_t x_39; uint8_t x_40; 
x_37 = 10;
x_38 = lean_string_utf8_next_fast(x_2, x_32);
x_39 = lean_string_utf8_get_fast(x_2, x_32);
x_40 = lean_uint32_dec_eq(x_39, x_37);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_32);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_38);
x_4 = x_41;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_inc_ref(x_1);
x_43 = l_String_Slice_slice_x21(x_1, x_31, x_32);
lean_dec(x_32);
lean_dec(x_31);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_38);
x_45 = lean_ctor_get(x_43, 0);
lean_inc_ref(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_43, 2);
lean_inc(x_47);
lean_dec_ref(x_43);
x_6 = x_44;
x_7 = x_45;
x_8 = x_46;
x_9 = x_47;
goto block_13;
}
}
else
{
lean_object* x_48; 
lean_dec(x_32);
x_48 = lean_box(1);
lean_inc(x_3);
lean_inc_ref(x_2);
x_6 = x_48;
x_7 = x_2;
x_8 = x_31;
x_9 = x_3;
goto block_13;
}
}
}
else
{
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
block_13:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_string_utf8_extract(x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_11 = lean_array_push(x_5, x_10);
x_4 = x_6;
x_5 = x_11;
goto _start;
}
}
}
static lean_object* _init_l_Lake_GitRepo_getTags___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_GitRepo_getTags___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_getTags___closed__0));
x_2 = l_Lake_GitRepo_getTags___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_3 = l_Lake_GitRepo_getTags___closed__2;
x_4 = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
x_5 = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lake_GitRepo_captureGit___closed__1;
x_9 = 1;
x_10 = 0;
x_11 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 2, x_3);
lean_ctor_set(x_11, 3, x_6);
lean_ctor_set(x_11, 4, x_8);
lean_ctor_set_uint8(x_11, sizeof(void*)*5, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*5 + 1, x_10);
x_12 = l_Lake_captureProc_x3f(x_11);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_string_utf8_byte_size(x_13);
lean_inc(x_13);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_7);
lean_ctor_set(x_15, 2, x_14);
x_16 = l_String_Slice_split___at___00Lake_GitRepo_getHeadRevisions_spec__0(x_15);
x_17 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getTags_spec__0___redArg(x_15, x_13, x_14, x_16, x_8);
x_18 = lean_array_to_list(x_17);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_12);
x_19 = lean_box(0);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_GitRepo_getTags(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getTags_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getTags_spec__0___redArg(x_1, x_2, x_3, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_findTag_x3f___closed__0));
x_2 = l_Lake_GitRepo_fetch___closed__3;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_fetch___closed__1));
x_2 = l_Lake_GitRepo_findTag_x3f___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_findTag_x3f___closed__1));
x_2 = l_Lake_GitRepo_findTag_x3f___closed__3;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_4 = l_Lake_GitRepo_findTag_x3f___closed__4;
x_5 = lean_array_push(x_4, x_1);
x_6 = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
x_7 = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = l_Lake_GitRepo_captureGit___closed__1;
x_10 = 1;
x_11 = 0;
x_12 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_5);
lean_ctor_set(x_12, 3, x_8);
lean_ctor_set(x_12, 4, x_9);
lean_ctor_set_uint8(x_12, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*5 + 1, x_11);
x_13 = l_Lake_captureProc_x3f(x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_GitRepo_findTag_x3f(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_getRemoteUrl_x3f___closed__0));
x_2 = l_Lake_GitRepo_clone___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_getRemoteUrl_x3f___closed__1));
x_2 = l_Lake_GitRepo_getRemoteUrl_x3f___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_4 = l_Lake_GitRepo_getRemoteUrl_x3f___closed__3;
x_5 = lean_array_push(x_4, x_1);
x_6 = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
x_7 = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = l_Lake_GitRepo_captureGit___closed__1;
x_10 = 1;
x_11 = 0;
x_12 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_5);
lean_ctor_set(x_12, 3, x_8);
lean_ctor_set(x_12, 4, x_9);
lean_ctor_set_uint8(x_12, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*5 + 1, x_11);
x_13 = l_Lake_captureProc_x3f(x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_GitRepo_getRemoteUrl_x3f(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_GitRepo_getRemoteUrl_x3f(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = l_Lake_Git_filterUrl_x3f(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_GitRepo_hasNoDiff___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_hasNoDiff___closed__0));
x_2 = l_Lake_GitRepo_clone___closed__1;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_hasNoDiff___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_getHeadRevision_x3f___closed__0));
x_2 = l_Lake_GitRepo_hasNoDiff___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_GitRepo_hasNoDiff___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lake_GitRepo_hasNoDiff___closed__1));
x_2 = l_Lake_GitRepo_hasNoDiff___closed__3;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasNoDiff(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; 
x_3 = l_Lake_GitRepo_hasNoDiff___closed__4;
x_4 = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
x_5 = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = l_Lake_GitRepo_captureGit___closed__1;
x_8 = 1;
x_9 = 0;
x_10 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_3);
lean_ctor_set(x_10, 3, x_6);
lean_ctor_set(x_10, 4, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*5 + 1, x_9);
x_11 = l_Lake_testProc(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasNoDiff___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_GitRepo_hasNoDiff(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasDiff(lean_object* x_1) {
_start:
{
uint8_t x_3; 
x_3 = l_Lake_GitRepo_hasNoDiff(x_1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasDiff___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_GitRepo_hasDiff(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Init_Data_ToString(uint8_t builtin);
lean_object* initialize_Lake_Util_Proc(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Git(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Proc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Git_filterUrl_x3f___closed__1 = _init_l_Lake_Git_filterUrl_x3f___closed__1();
lean_mark_persistent(l_Lake_Git_filterUrl_x3f___closed__1);
l_Lake_Git_filterUrl_x3f___closed__3 = _init_l_Lake_Git_filterUrl_x3f___closed__3();
lean_mark_persistent(l_Lake_Git_filterUrl_x3f___closed__3);
l_Lake_GitRepo_captureGit___closed__1 = _init_l_Lake_GitRepo_captureGit___closed__1();
lean_mark_persistent(l_Lake_GitRepo_captureGit___closed__1);
l_Lake_GitRepo_clone___closed__1 = _init_l_Lake_GitRepo_clone___closed__1();
lean_mark_persistent(l_Lake_GitRepo_clone___closed__1);
l_Lake_GitRepo_clone___closed__2 = _init_l_Lake_GitRepo_clone___closed__2();
lean_mark_persistent(l_Lake_GitRepo_clone___closed__2);
l_Lake_GitRepo_quietInit___closed__2 = _init_l_Lake_GitRepo_quietInit___closed__2();
lean_mark_persistent(l_Lake_GitRepo_quietInit___closed__2);
l_Lake_GitRepo_quietInit___closed__3 = _init_l_Lake_GitRepo_quietInit___closed__3();
lean_mark_persistent(l_Lake_GitRepo_quietInit___closed__3);
l_Lake_GitRepo_quietInit___closed__4 = _init_l_Lake_GitRepo_quietInit___closed__4();
lean_mark_persistent(l_Lake_GitRepo_quietInit___closed__4);
l_Lake_GitRepo_insideWorkTree___closed__2 = _init_l_Lake_GitRepo_insideWorkTree___closed__2();
lean_mark_persistent(l_Lake_GitRepo_insideWorkTree___closed__2);
l_Lake_GitRepo_insideWorkTree___closed__3 = _init_l_Lake_GitRepo_insideWorkTree___closed__3();
lean_mark_persistent(l_Lake_GitRepo_insideWorkTree___closed__3);
l_Lake_GitRepo_fetch___closed__3 = _init_l_Lake_GitRepo_fetch___closed__3();
lean_mark_persistent(l_Lake_GitRepo_fetch___closed__3);
l_Lake_GitRepo_fetch___closed__4 = _init_l_Lake_GitRepo_fetch___closed__4();
lean_mark_persistent(l_Lake_GitRepo_fetch___closed__4);
l_Lake_GitRepo_fetch___closed__5 = _init_l_Lake_GitRepo_fetch___closed__5();
lean_mark_persistent(l_Lake_GitRepo_fetch___closed__5);
l_Lake_GitRepo_fetch___closed__6 = _init_l_Lake_GitRepo_fetch___closed__6();
lean_mark_persistent(l_Lake_GitRepo_fetch___closed__6);
l_Lake_GitRepo_checkoutBranch___closed__2 = _init_l_Lake_GitRepo_checkoutBranch___closed__2();
lean_mark_persistent(l_Lake_GitRepo_checkoutBranch___closed__2);
l_Lake_GitRepo_checkoutBranch___closed__3 = _init_l_Lake_GitRepo_checkoutBranch___closed__3();
lean_mark_persistent(l_Lake_GitRepo_checkoutBranch___closed__3);
l_Lake_GitRepo_checkoutDetach___closed__2 = _init_l_Lake_GitRepo_checkoutDetach___closed__2();
lean_mark_persistent(l_Lake_GitRepo_checkoutDetach___closed__2);
l_Lake_GitRepo_checkoutDetach___closed__3 = _init_l_Lake_GitRepo_checkoutDetach___closed__3();
lean_mark_persistent(l_Lake_GitRepo_checkoutDetach___closed__3);
l_Lake_GitRepo_resolveRevision_x3f___closed__2 = _init_l_Lake_GitRepo_resolveRevision_x3f___closed__2();
lean_mark_persistent(l_Lake_GitRepo_resolveRevision_x3f___closed__2);
l_Lake_GitRepo_resolveRevision_x3f___closed__3 = _init_l_Lake_GitRepo_resolveRevision_x3f___closed__3();
lean_mark_persistent(l_Lake_GitRepo_resolveRevision_x3f___closed__3);
l_Lake_GitRepo_resolveRevision_x3f___closed__4 = _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4();
lean_mark_persistent(l_Lake_GitRepo_resolveRevision_x3f___closed__4);
l_Std_Iter_toStringArray___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg___closed__0 = _init_l_Std_Iter_toStringArray___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg___closed__0();
lean_mark_persistent(l_Std_Iter_toStringArray___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg___closed__0);
l_Lake_GitRepo_getHeadRevisions___closed__1 = _init_l_Lake_GitRepo_getHeadRevisions___closed__1();
lean_mark_persistent(l_Lake_GitRepo_getHeadRevisions___closed__1);
l_Lake_GitRepo_getHeadRevisions___closed__2 = _init_l_Lake_GitRepo_getHeadRevisions___closed__2();
lean_mark_persistent(l_Lake_GitRepo_getHeadRevisions___closed__2);
l_Lake_GitRepo_getHeadRevisions___closed__4 = _init_l_Lake_GitRepo_getHeadRevisions___closed__4();
lean_mark_persistent(l_Lake_GitRepo_getHeadRevisions___closed__4);
l_Lake_GitRepo_branchExists___closed__2 = _init_l_Lake_GitRepo_branchExists___closed__2();
lean_mark_persistent(l_Lake_GitRepo_branchExists___closed__2);
l_Lake_GitRepo_branchExists___closed__3 = _init_l_Lake_GitRepo_branchExists___closed__3();
lean_mark_persistent(l_Lake_GitRepo_branchExists___closed__3);
l_Lake_GitRepo_revisionExists___closed__1 = _init_l_Lake_GitRepo_revisionExists___closed__1();
lean_mark_persistent(l_Lake_GitRepo_revisionExists___closed__1);
l_Lake_GitRepo_revisionExists___closed__2 = _init_l_Lake_GitRepo_revisionExists___closed__2();
lean_mark_persistent(l_Lake_GitRepo_revisionExists___closed__2);
l_Lake_GitRepo_getTags___closed__1 = _init_l_Lake_GitRepo_getTags___closed__1();
lean_mark_persistent(l_Lake_GitRepo_getTags___closed__1);
l_Lake_GitRepo_getTags___closed__2 = _init_l_Lake_GitRepo_getTags___closed__2();
lean_mark_persistent(l_Lake_GitRepo_getTags___closed__2);
l_Lake_GitRepo_findTag_x3f___closed__2 = _init_l_Lake_GitRepo_findTag_x3f___closed__2();
lean_mark_persistent(l_Lake_GitRepo_findTag_x3f___closed__2);
l_Lake_GitRepo_findTag_x3f___closed__3 = _init_l_Lake_GitRepo_findTag_x3f___closed__3();
lean_mark_persistent(l_Lake_GitRepo_findTag_x3f___closed__3);
l_Lake_GitRepo_findTag_x3f___closed__4 = _init_l_Lake_GitRepo_findTag_x3f___closed__4();
lean_mark_persistent(l_Lake_GitRepo_findTag_x3f___closed__4);
l_Lake_GitRepo_getRemoteUrl_x3f___closed__2 = _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__2();
lean_mark_persistent(l_Lake_GitRepo_getRemoteUrl_x3f___closed__2);
l_Lake_GitRepo_getRemoteUrl_x3f___closed__3 = _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__3();
lean_mark_persistent(l_Lake_GitRepo_getRemoteUrl_x3f___closed__3);
l_Lake_GitRepo_hasNoDiff___closed__2 = _init_l_Lake_GitRepo_hasNoDiff___closed__2();
lean_mark_persistent(l_Lake_GitRepo_hasNoDiff___closed__2);
l_Lake_GitRepo_hasNoDiff___closed__3 = _init_l_Lake_GitRepo_hasNoDiff___closed__3();
lean_mark_persistent(l_Lake_GitRepo_hasNoDiff___closed__3);
l_Lake_GitRepo_hasNoDiff___closed__4 = _init_l_Lake_GitRepo_hasNoDiff___closed__4();
lean_mark_persistent(l_Lake_GitRepo_hasNoDiff___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
