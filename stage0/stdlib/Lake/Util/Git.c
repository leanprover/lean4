// Lean compiler output
// Module: Lake.Util.Git
// Imports: public import Init.Data.ToString public import Lake.Util.Proc import Init.Data.String.TakeDrop import Init.Data.String.Search import Lake.Util.String
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lake_captureProc_x3f(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_testProc(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lake_mkCmdLog(lean_object*);
lean_object* l_IO_Process_output(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t l_Lake_isHex(lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
uint8_t l_System_FilePath_pathExists(lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
lean_object* l_Lake_captureProc_x27(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static const lean_string_object l_Lake_Git_defaultRemote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "origin"};
static const lean_object* l_Lake_Git_defaultRemote___closed__0 = (const lean_object*)&l_Lake_Git_defaultRemote___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Git_defaultRemote = (const lean_object*)&l_Lake_Git_defaultRemote___closed__0_value;
static const lean_string_object l_Lake_Git_upstreamBranch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "master"};
static const lean_object* l_Lake_Git_upstreamBranch___closed__0 = (const lean_object*)&l_Lake_Git_upstreamBranch___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Git_upstreamBranch = (const lean_object*)&l_Lake_Git_upstreamBranch___closed__0_value;
static const lean_string_object l_Lake_Git_filterUrl_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = ".git"};
static const lean_object* l_Lake_Git_filterUrl_x3f___closed__0 = (const lean_object*)&l_Lake_Git_filterUrl_x3f___closed__0_value;
static lean_once_cell_t l_Lake_Git_filterUrl_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Git_filterUrl_x3f___closed__1;
static const lean_string_object l_Lake_Git_filterUrl_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "git"};
static const lean_object* l_Lake_Git_filterUrl_x3f___closed__2 = (const lean_object*)&l_Lake_Git_filterUrl_x3f___closed__2_value;
static lean_once_cell_t l_Lake_Git_filterUrl_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Git_filterUrl_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lake_Git_filterUrl_x3f(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Git_isFullObjectName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Git_isFullObjectName___boxed(lean_object*);
static const lean_string_object l_Lake_GitRev_head___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l_Lake_GitRev_head___closed__0 = (const lean_object*)&l_Lake_GitRev_head___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_GitRev_head = (const lean_object*)&l_Lake_GitRev_head___closed__0_value;
static const lean_string_object l_Lake_GitRev_fetchHead___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "FETCH_HEAD"};
static const lean_object* l_Lake_GitRev_fetchHead___closed__0 = (const lean_object*)&l_Lake_GitRev_fetchHead___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_GitRev_fetchHead = (const lean_object*)&l_Lake_GitRev_fetchHead___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_GitRev_isFullSha1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRev_isFullSha1___boxed(lean_object*);
static const lean_string_object l_Lake_GitRev_withRemote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Lake_GitRev_withRemote___closed__0 = (const lean_object*)&l_Lake_GitRev_withRemote___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_GitRev_withRemote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRev_withRemote___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_instCoeFilePath___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_instCoeFilePath___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_GitRepo_instCoeFilePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_GitRepo_instCoeFilePath___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_GitRepo_instCoeFilePath___closed__0 = (const lean_object*)&l_Lake_GitRepo_instCoeFilePath___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_GitRepo_instCoeFilePath = (const lean_object*)&l_Lake_GitRepo_instCoeFilePath___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_GitRepo_instToString = (const lean_object*)&l_Lake_GitRepo_instCoeFilePath___closed__0_value;
static const lean_string_object l_Lake_GitRepo_cwd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_GitRepo_cwd___closed__0 = (const lean_object*)&l_Lake_GitRepo_cwd___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_GitRepo_cwd = (const lean_object*)&l_Lake_GitRepo_cwd___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_GitRepo_dirExists(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_dirExists___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_GitRepo_gitExists(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_gitExists___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lake_GitRepo_captureGit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_GitRepo_captureGit___closed__0 = (const lean_object*)&l_Lake_GitRepo_captureGit___closed__0_value;
static const lean_array_object l_Lake_GitRepo_captureGit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_GitRepo_captureGit___closed__1 = (const lean_object*)&l_Lake_GitRepo_captureGit___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_GitRepo_testGit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_testGit___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__0(uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "stderr:\n"};
static const lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1___closed__0 = (const lean_object*)&l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "stdout:\n"};
static const lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___closed__0 = (const lean_object*)&l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___closed__0_value;
static const lean_string_object l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "failed to execute 'git': "};
static const lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___closed__1 = (const lean_object*)&l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_clone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "clone"};
static const lean_object* l_Lake_GitRepo_clone___closed__0 = (const lean_object*)&l_Lake_GitRepo_clone___closed__0_value;
static lean_once_cell_t l_Lake_GitRepo_clone___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_clone___closed__1;
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_quietInit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "init"};
static const lean_object* l_Lake_GitRepo_quietInit___closed__0 = (const lean_object*)&l_Lake_GitRepo_quietInit___closed__0_value;
static const lean_string_object l_Lake_GitRepo_quietInit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-q"};
static const lean_object* l_Lake_GitRepo_quietInit___closed__1 = (const lean_object*)&l_Lake_GitRepo_quietInit___closed__1_value;
static const lean_array_object l_Lake_GitRepo_quietInit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_quietInit___closed__0_value),((lean_object*)&l_Lake_GitRepo_quietInit___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_quietInit___closed__2 = (const lean_object*)&l_Lake_GitRepo_quietInit___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_bareInit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "--bare"};
static const lean_object* l_Lake_GitRepo_bareInit___closed__0 = (const lean_object*)&l_Lake_GitRepo_bareInit___closed__0_value;
static const lean_array_object l_Lake_GitRepo_bareInit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_Lake_GitRepo_quietInit___closed__0_value),((lean_object*)&l_Lake_GitRepo_bareInit___closed__0_value),((lean_object*)&l_Lake_GitRepo_quietInit___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_bareInit___closed__1 = (const lean_object*)&l_Lake_GitRepo_bareInit___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_bareInit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_bareInit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_insideWorkTree___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rev-parse"};
static const lean_object* l_Lake_GitRepo_insideWorkTree___closed__0 = (const lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__0_value;
static const lean_string_object l_Lake_GitRepo_insideWorkTree___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "--is-inside-work-tree"};
static const lean_object* l_Lake_GitRepo_insideWorkTree___closed__1 = (const lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__1_value;
static const lean_array_object l_Lake_GitRepo_insideWorkTree___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__0_value),((lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_insideWorkTree___closed__2 = (const lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__2_value;
LEAN_EXPORT uint8_t l_Lake_GitRepo_insideWorkTree(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_insideWorkTree___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_fetch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "fetch"};
static const lean_object* l_Lake_GitRepo_fetch___closed__0 = (const lean_object*)&l_Lake_GitRepo_fetch___closed__0_value;
static const lean_string_object l_Lake_GitRepo_fetch___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "--tags"};
static const lean_object* l_Lake_GitRepo_fetch___closed__1 = (const lean_object*)&l_Lake_GitRepo_fetch___closed__1_value;
static const lean_string_object l_Lake_GitRepo_fetch___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "--force"};
static const lean_object* l_Lake_GitRepo_fetch___closed__2 = (const lean_object*)&l_Lake_GitRepo_fetch___closed__2_value;
static lean_once_cell_t l_Lake_GitRepo_fetch___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetch___closed__3;
static lean_once_cell_t l_Lake_GitRepo_fetch___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetch___closed__4;
static lean_once_cell_t l_Lake_GitRepo_fetch___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetch___closed__5;
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_addWorktreeDetach___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "worktree"};
static const lean_object* l_Lake_GitRepo_addWorktreeDetach___closed__0 = (const lean_object*)&l_Lake_GitRepo_addWorktreeDetach___closed__0_value;
static const lean_string_object l_Lake_GitRepo_addWorktreeDetach___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l_Lake_GitRepo_addWorktreeDetach___closed__1 = (const lean_object*)&l_Lake_GitRepo_addWorktreeDetach___closed__1_value;
static const lean_string_object l_Lake_GitRepo_addWorktreeDetach___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "--detach"};
static const lean_object* l_Lake_GitRepo_addWorktreeDetach___closed__2 = (const lean_object*)&l_Lake_GitRepo_addWorktreeDetach___closed__2_value;
static lean_once_cell_t l_Lake_GitRepo_addWorktreeDetach___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_addWorktreeDetach___closed__3;
static lean_once_cell_t l_Lake_GitRepo_addWorktreeDetach___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_addWorktreeDetach___closed__4;
static lean_once_cell_t l_Lake_GitRepo_addWorktreeDetach___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_addWorktreeDetach___closed__5;
LEAN_EXPORT lean_object* l_Lake_GitRepo_addWorktreeDetach(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_addWorktreeDetach___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_checkoutBranch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "checkout"};
static const lean_object* l_Lake_GitRepo_checkoutBranch___closed__0 = (const lean_object*)&l_Lake_GitRepo_checkoutBranch___closed__0_value;
static const lean_string_object l_Lake_GitRepo_checkoutBranch___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-B"};
static const lean_object* l_Lake_GitRepo_checkoutBranch___closed__1 = (const lean_object*)&l_Lake_GitRepo_checkoutBranch___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_checkoutBranch___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_checkoutBranch___closed__2;
static lean_once_cell_t l_Lake_GitRepo_checkoutBranch___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_checkoutBranch___closed__3;
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_checkoutDetach___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "--"};
static const lean_object* l_Lake_GitRepo_checkoutDetach___closed__0 = (const lean_object*)&l_Lake_GitRepo_checkoutDetach___closed__0_value;
static lean_once_cell_t l_Lake_GitRepo_checkoutDetach___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_checkoutDetach___closed__1;
static lean_once_cell_t l_Lake_GitRepo_checkoutDetach___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_checkoutDetach___closed__2;
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_gcAuto___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "gc"};
static const lean_object* l_Lake_GitRepo_gcAuto___closed__0 = (const lean_object*)&l_Lake_GitRepo_gcAuto___closed__0_value;
static const lean_string_object l_Lake_GitRepo_gcAuto___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "--auto"};
static const lean_object* l_Lake_GitRepo_gcAuto___closed__1 = (const lean_object*)&l_Lake_GitRepo_gcAuto___closed__1_value;
static const lean_array_object l_Lake_GitRepo_gcAuto___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_gcAuto___closed__0_value),((lean_object*)&l_Lake_GitRepo_gcAuto___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_gcAuto___closed__2 = (const lean_object*)&l_Lake_GitRepo_gcAuto___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_gcAuto(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_gcAuto___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_clean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "clean"};
static const lean_object* l_Lake_GitRepo_clean___closed__0 = (const lean_object*)&l_Lake_GitRepo_clean___closed__0_value;
static const lean_string_object l_Lake_GitRepo_clean___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "-xf"};
static const lean_object* l_Lake_GitRepo_clean___closed__1 = (const lean_object*)&l_Lake_GitRepo_clean___closed__1_value;
static const lean_array_object l_Lake_GitRepo_clean___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_clean___closed__0_value),((lean_object*)&l_Lake_GitRepo_clean___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_clean___closed__2 = (const lean_object*)&l_Lake_GitRepo_clean___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_clean(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_clean___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_resolveRevision_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "--verify"};
static const lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_resolveRevision_x3f___closed__0_value;
static const lean_string_object l_Lake_GitRepo_resolveRevision_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "--end-of-options"};
static const lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__1 = (const lean_object*)&l_Lake_GitRepo_resolveRevision_x3f___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_resolveRevision_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__2;
static lean_once_cell_t l_Lake_GitRepo_resolveRevision_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__3;
static lean_once_cell_t l_Lake_GitRepo_resolveRevision_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_findCommit_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "^{commit}"};
static const lean_object* l_Lake_GitRepo_findCommit_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_findCommit_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_findCommit_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findCommit_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_resolveRevision___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = ": revision not found '"};
static const lean_object* l_Lake_GitRepo_resolveRevision___closed__0 = (const lean_object*)&l_Lake_GitRepo_resolveRevision___closed__0_value;
static const lean_string_object l_Lake_GitRepo_resolveRevision___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lake_GitRepo_resolveRevision___closed__1 = (const lean_object*)&l_Lake_GitRepo_resolveRevision___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getHeadRevision___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 114, .m_capacity = 114, .m_length = 113, .m_data = ": could not resolve 'HEAD' to a commit; the repository may be corrupt, so you may need to remove it and try again"};
static const lean_object* l_Lake_GitRepo_getHeadRevision___closed__0 = (const lean_object*)&l_Lake_GitRepo_getHeadRevision___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_fetchRevision_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "--filter=tree:0"};
static const lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_fetchRevision_x3f___closed__0_value;
static lean_once_cell_t l_Lake_GitRepo_fetchRevision_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__1;
static lean_once_cell_t l_Lake_GitRepo_fetchRevision_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__2;
static lean_once_cell_t l_Lake_GitRepo_fetchRevision_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__3;
static lean_once_cell_t l_Lake_GitRepo_fetchRevision_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__4;
static const lean_string_object l_Lake_GitRepo_fetchRevision_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 110, .m_capacity = 110, .m_length = 109, .m_data = ": could not resolve 'FETCH_HEAD' to a commit after fetching; this may be an issue with Lake; please report it"};
static const lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__5 = (const lean_object*)&l_Lake_GitRepo_fetchRevision_x3f___closed__5_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetchRevision_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetchRevision_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getHeadRevisions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rev-list"};
static const lean_object* l_Lake_GitRepo_getHeadRevisions___closed__0 = (const lean_object*)&l_Lake_GitRepo_getHeadRevisions___closed__0_value;
static const lean_array_object l_Lake_GitRepo_getHeadRevisions___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_getHeadRevisions___closed__0_value),((lean_object*)&l_Lake_GitRev_head___closed__0_value)}};
static const lean_object* l_Lake_GitRepo_getHeadRevisions___closed__1 = (const lean_object*)&l_Lake_GitRepo_getHeadRevisions___closed__1_value;
static const lean_string_object l_Lake_GitRepo_getHeadRevisions___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-n"};
static const lean_object* l_Lake_GitRepo_getHeadRevisions___closed__2 = (const lean_object*)&l_Lake_GitRepo_getHeadRevisions___closed__2_value;
static lean_once_cell_t l_Lake_GitRepo_getHeadRevisions___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_getHeadRevisions___closed__3;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_branchExists___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "show-ref"};
static const lean_object* l_Lake_GitRepo_branchExists___closed__0 = (const lean_object*)&l_Lake_GitRepo_branchExists___closed__0_value;
static const lean_string_object l_Lake_GitRepo_branchExists___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "refs/heads/"};
static const lean_object* l_Lake_GitRepo_branchExists___closed__1 = (const lean_object*)&l_Lake_GitRepo_branchExists___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_branchExists___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_branchExists___closed__2;
static lean_once_cell_t l_Lake_GitRepo_branchExists___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_branchExists___closed__3;
LEAN_EXPORT uint8_t l_Lake_GitRepo_branchExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_branchExists___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_GitRepo_revisionExists___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_revisionExists___closed__0;
static lean_once_cell_t l_Lake_GitRepo_revisionExists___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_revisionExists___closed__1;
LEAN_EXPORT uint8_t l_Lake_GitRepo_revisionExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_revisionExists___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getTags___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "tag"};
static const lean_object* l_Lake_GitRepo_getTags___closed__0 = (const lean_object*)&l_Lake_GitRepo_getTags___closed__0_value;
static const lean_array_object l_Lake_GitRepo_getTags___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lake_GitRepo_getTags___closed__0_value)}};
static const lean_object* l_Lake_GitRepo_getTags___closed__1 = (const lean_object*)&l_Lake_GitRepo_getTags___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_findTag_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "describe"};
static const lean_object* l_Lake_GitRepo_findTag_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_findTag_x3f___closed__0_value;
static const lean_string_object l_Lake_GitRepo_findTag_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "--exact-match"};
static const lean_object* l_Lake_GitRepo_findTag_x3f___closed__1 = (const lean_object*)&l_Lake_GitRepo_findTag_x3f___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_findTag_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__2;
static lean_once_cell_t l_Lake_GitRepo_findTag_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__3;
static lean_once_cell_t l_Lake_GitRepo_findTag_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getRemoteUrl_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "remote"};
static const lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_getRemoteUrl_x3f___closed__0_value;
static const lean_string_object l_Lake_GitRepo_getRemoteUrl_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "get-url"};
static const lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__1 = (const lean_object*)&l_Lake_GitRepo_getRemoteUrl_x3f___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_getRemoteUrl_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__2;
static lean_once_cell_t l_Lake_GitRepo_getRemoteUrl_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_GitRepo_addRemote___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_addRemote___closed__0;
static lean_once_cell_t l_Lake_GitRepo_addRemote___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_addRemote___closed__1;
LEAN_EXPORT lean_object* l_Lake_GitRepo_addRemote(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_addRemote___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_setRemoteUrl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "set-url"};
static const lean_object* l_Lake_GitRepo_setRemoteUrl___closed__0 = (const lean_object*)&l_Lake_GitRepo_setRemoteUrl___closed__0_value;
static lean_once_cell_t l_Lake_GitRepo_setRemoteUrl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_setRemoteUrl___closed__1;
LEAN_EXPORT lean_object* l_Lake_GitRepo_setRemoteUrl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_setRemoteUrl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_pruneRemote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "prune"};
static const lean_object* l_Lake_GitRepo_pruneRemote___closed__0 = (const lean_object*)&l_Lake_GitRepo_pruneRemote___closed__0_value;
static lean_once_cell_t l_Lake_GitRepo_pruneRemote___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_pruneRemote___closed__1;
LEAN_EXPORT lean_object* l_Lake_GitRepo_pruneRemote(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_pruneRemote___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_hasNoDiff___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "diff"};
static const lean_object* l_Lake_GitRepo_hasNoDiff___closed__0 = (const lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__0_value;
static const lean_string_object l_Lake_GitRepo_hasNoDiff___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "--exit-code"};
static const lean_object* l_Lake_GitRepo_hasNoDiff___closed__1 = (const lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__1_value;
static const lean_array_object l_Lake_GitRepo_hasNoDiff___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__0_value),((lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__1_value),((lean_object*)&l_Lake_GitRev_head___closed__0_value)}};
static const lean_object* l_Lake_GitRepo_hasNoDiff___closed__2 = (const lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__2_value;
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasNoDiff(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasNoDiff___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasDiff(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasDiff___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Lake_Git_filterUrl_x3f___closed__1(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_6_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__0));
v___x_7_ = lean_string_utf8_byte_size(v___x_6_);
return v___x_7_;
}
}
static lean_object* _init_l_Lake_Git_filterUrl_x3f___closed__3(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_10_ = lean_string_utf8_byte_size(v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lake_Git_filterUrl_x3f(lean_object* v_url_11_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_27_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_28_ = lean_string_utf8_byte_size(v_url_11_);
v___x_29_ = lean_obj_once(&l_Lake_Git_filterUrl_x3f___closed__3, &l_Lake_Git_filterUrl_x3f___closed__3_once, _init_l_Lake_Git_filterUrl_x3f___closed__3);
v___x_30_ = lean_nat_dec_le(v___x_29_, v___x_28_);
if (v___x_30_ == 0)
{
goto v___jp_12_;
}
else
{
lean_object* v___x_31_; uint8_t v___x_32_; 
v___x_31_ = lean_unsigned_to_nat(0u);
v___x_32_ = lean_string_memcmp(v_url_11_, v___x_27_, v___x_31_, v___x_31_, v___x_29_);
if (v___x_32_ == 0)
{
goto v___jp_12_;
}
else
{
lean_object* v___x_33_; 
lean_dec_ref(v_url_11_);
v___x_33_ = lean_box(0);
return v___x_33_;
}
}
v___jp_12_:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; uint8_t v___x_16_; 
v___x_13_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__0));
v___x_14_ = lean_string_utf8_byte_size(v_url_11_);
v___x_15_ = lean_obj_once(&l_Lake_Git_filterUrl_x3f___closed__1, &l_Lake_Git_filterUrl_x3f___closed__1_once, _init_l_Lake_Git_filterUrl_x3f___closed__1);
v___x_16_ = lean_nat_dec_le(v___x_15_, v___x_14_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; 
v___x_17_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_17_, 0, v_url_11_);
return v___x_17_;
}
else
{
lean_object* v___x_18_; lean_object* v___x_19_; uint8_t v___x_20_; 
v___x_18_ = lean_unsigned_to_nat(0u);
v___x_19_ = lean_nat_sub(v___x_14_, v___x_15_);
v___x_20_ = lean_string_memcmp(v_url_11_, v___x_13_, v___x_19_, v___x_18_, v___x_15_);
lean_dec(v___x_19_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; 
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v_url_11_);
return v___x_21_;
}
else
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_22_ = lean_unsigned_to_nat(4u);
lean_inc_ref(v_url_11_);
v___x_23_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_23_, 0, v_url_11_);
lean_ctor_set(v___x_23_, 1, v___x_18_);
lean_ctor_set(v___x_23_, 2, v___x_14_);
v___x_24_ = l_String_Slice_Pos_prevn(v___x_23_, v___x_14_, v___x_22_);
lean_dec_ref_known(v___x_23_, 3);
v___x_25_ = lean_string_utf8_extract_fast(v_url_11_, v___x_18_, v___x_24_);
lean_dec(v___x_24_);
lean_dec_ref(v_url_11_);
v___x_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_Git_isFullObjectName(lean_object* v_rev_34_){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; uint8_t v___x_37_; 
v___x_35_ = lean_string_utf8_byte_size(v_rev_34_);
v___x_36_ = lean_unsigned_to_nat(40u);
v___x_37_ = lean_nat_dec_eq(v___x_35_, v___x_36_);
if (v___x_37_ == 0)
{
return v___x_37_;
}
else
{
uint8_t v___x_38_; 
v___x_38_ = l_Lake_isHex(v_rev_34_);
return v___x_38_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Git_isFullObjectName___boxed(lean_object* v_rev_39_){
_start:
{
uint8_t v_res_40_; lean_object* v_r_41_; 
v_res_40_ = l_Lake_Git_isFullObjectName(v_rev_39_);
lean_dec_ref(v_rev_39_);
v_r_41_ = lean_box(v_res_40_);
return v_r_41_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRev_isFullSha1(lean_object* v_rev_46_){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; uint8_t v___x_49_; 
v___x_47_ = lean_string_utf8_byte_size(v_rev_46_);
v___x_48_ = lean_unsigned_to_nat(40u);
v___x_49_ = lean_nat_dec_eq(v___x_47_, v___x_48_);
if (v___x_49_ == 0)
{
return v___x_49_;
}
else
{
uint8_t v___x_50_; 
v___x_50_ = l_Lake_isHex(v_rev_46_);
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRev_isFullSha1___boxed(lean_object* v_rev_51_){
_start:
{
uint8_t v_res_52_; lean_object* v_r_53_; 
v_res_52_ = l_Lake_GitRev_isFullSha1(v_rev_51_);
lean_dec_ref(v_rev_51_);
v_r_53_ = lean_box(v_res_52_);
return v_r_53_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRev_withRemote(lean_object* v_remote_55_, lean_object* v_rev_56_){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_57_ = ((lean_object*)(l_Lake_GitRev_withRemote___closed__0));
v___x_58_ = lean_string_append(v_remote_55_, v___x_57_);
v___x_59_ = lean_string_append(v___x_58_, v_rev_56_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRev_withRemote___boxed(lean_object* v_remote_60_, lean_object* v_rev_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lake_GitRev_withRemote(v_remote_60_, v_rev_61_);
lean_dec_ref(v_rev_61_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_instCoeFilePath___lam__0(lean_object* v_x_63_){
_start:
{
lean_inc_ref(v_x_63_);
return v_x_63_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_instCoeFilePath___lam__0___boxed(lean_object* v_x_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lake_GitRepo_instCoeFilePath___lam__0(v_x_64_);
lean_dec_ref(v_x_64_);
return v_res_65_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_dirExists(lean_object* v_repo_71_){
_start:
{
uint8_t v___x_73_; 
v___x_73_ = l_System_FilePath_isDir(v_repo_71_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_dirExists___boxed(lean_object* v_repo_74_, lean_object* v_a_75_){
_start:
{
uint8_t v_res_76_; lean_object* v_r_77_; 
v_res_76_ = l_Lake_GitRepo_dirExists(v_repo_74_);
lean_dec_ref(v_repo_74_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_gitExists(lean_object* v_repo_78_){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_80_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__0));
v___x_81_ = l_System_FilePath_join(v_repo_78_, v___x_80_);
v___x_82_ = l_System_FilePath_pathExists(v___x_81_);
lean_dec_ref(v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_gitExists___boxed(lean_object* v_repo_83_, lean_object* v_a_84_){
_start:
{
uint8_t v_res_85_; lean_object* v_r_86_; 
v_res_85_ = l_Lake_GitRepo_gitExists(v_repo_83_);
v_r_86_ = lean_box(v_res_85_);
return v_r_86_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit(lean_object* v_args_91_, lean_object* v_repo_92_, lean_object* v_a_93_){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; uint8_t v___x_100_; uint8_t v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_95_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_96_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_97_, 0, v_repo_92_);
v___x_98_ = lean_unsigned_to_nat(0u);
v___x_99_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_100_ = 1;
v___x_101_ = 0;
v___x_102_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_102_, 0, v___x_95_);
lean_ctor_set(v___x_102_, 1, v___x_96_);
lean_ctor_set(v___x_102_, 2, v_args_91_);
lean_ctor_set(v___x_102_, 3, v___x_97_);
lean_ctor_set(v___x_102_, 4, v___x_99_);
lean_ctor_set_uint8(v___x_102_, sizeof(void*)*5, v___x_100_);
lean_ctor_set_uint8(v___x_102_, sizeof(void*)*5 + 1, v___x_101_);
v___x_103_ = l_Lake_captureProc_x27(v___x_102_, v_a_93_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v_a_104_; lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_120_; 
v_a_104_ = lean_ctor_get(v___x_103_, 0);
v_a_105_ = lean_ctor_get(v___x_103_, 1);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_120_ == 0)
{
v___x_107_ = v___x_103_;
v_isShared_108_ = v_isSharedCheck_120_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_inc(v_a_104_);
lean_dec(v___x_103_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_120_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v_stdout_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v_str_113_; lean_object* v_startInclusive_114_; lean_object* v_endExclusive_115_; lean_object* v___x_116_; lean_object* v___x_118_; 
v_stdout_109_ = lean_ctor_get(v_a_104_, 0);
lean_inc_ref(v_stdout_109_);
lean_dec(v_a_104_);
v___x_110_ = lean_string_utf8_byte_size(v_stdout_109_);
v___x_111_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_111_, 0, v_stdout_109_);
lean_ctor_set(v___x_111_, 1, v___x_98_);
lean_ctor_set(v___x_111_, 2, v___x_110_);
v___x_112_ = l_String_Slice_trimAscii(v___x_111_);
v_str_113_ = lean_ctor_get(v___x_112_, 0);
lean_inc_ref(v_str_113_);
v_startInclusive_114_ = lean_ctor_get(v___x_112_, 1);
lean_inc(v_startInclusive_114_);
v_endExclusive_115_ = lean_ctor_get(v___x_112_, 2);
lean_inc(v_endExclusive_115_);
lean_dec_ref(v___x_112_);
v___x_116_ = lean_string_utf8_extract_fast(v_str_113_, v_startInclusive_114_, v_endExclusive_115_);
lean_dec(v_endExclusive_115_);
lean_dec(v_startInclusive_114_);
lean_dec_ref(v_str_113_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 0, v___x_116_);
v___x_118_ = v___x_107_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_116_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v_a_105_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
else
{
lean_object* v_a_121_; lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_129_; 
v_a_121_ = lean_ctor_get(v___x_103_, 0);
v_a_122_ = lean_ctor_get(v___x_103_, 1);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_129_ == 0)
{
v___x_124_ = v___x_103_;
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_inc(v_a_121_);
lean_dec(v___x_103_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_127_; 
if (v_isShared_125_ == 0)
{
v___x_127_ = v___x_124_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_a_121_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v_a_122_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit___boxed(lean_object* v_args_130_, lean_object* v_repo_131_, lean_object* v_a_132_, lean_object* v_a_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lake_GitRepo_captureGit(v_args_130_, v_repo_131_, v_a_132_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f(lean_object* v_args_135_, lean_object* v_repo_136_){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; uint8_t v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_138_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_139_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_140_, 0, v_repo_136_);
v___x_141_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_142_ = 1;
v___x_143_ = 0;
v___x_144_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_144_, 0, v___x_138_);
lean_ctor_set(v___x_144_, 1, v___x_139_);
lean_ctor_set(v___x_144_, 2, v_args_135_);
lean_ctor_set(v___x_144_, 3, v___x_140_);
lean_ctor_set(v___x_144_, 4, v___x_141_);
lean_ctor_set_uint8(v___x_144_, sizeof(void*)*5, v___x_142_);
lean_ctor_set_uint8(v___x_144_, sizeof(void*)*5 + 1, v___x_143_);
v___x_145_ = l_Lake_captureProc_x3f(v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f___boxed(lean_object* v_args_146_, lean_object* v_repo_147_, lean_object* v_a_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lake_GitRepo_captureGit_x3f(v_args_146_, v_repo_147_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit(lean_object* v_args_150_, lean_object* v_repo_151_, lean_object* v_a_152_){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; uint8_t v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_154_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_155_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_156_, 0, v_repo_151_);
v___x_157_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_158_ = 1;
v___x_159_ = 0;
v___x_160_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_160_, 0, v___x_154_);
lean_ctor_set(v___x_160_, 1, v___x_155_);
lean_ctor_set(v___x_160_, 2, v_args_150_);
lean_ctor_set(v___x_160_, 3, v___x_156_);
lean_ctor_set(v___x_160_, 4, v___x_157_);
lean_ctor_set_uint8(v___x_160_, sizeof(void*)*5, v___x_158_);
lean_ctor_set_uint8(v___x_160_, sizeof(void*)*5 + 1, v___x_159_);
v___x_161_ = lean_box(0);
v___x_162_ = l_Lake_proc(v___x_160_, v___x_158_, v___x_161_, v_a_152_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit___boxed(lean_object* v_args_163_, lean_object* v_repo_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lake_GitRepo_execGit(v_args_163_, v_repo_164_, v_a_165_);
return v_res_167_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_testGit(lean_object* v_args_168_, lean_object* v_repo_169_){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; uint8_t v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_171_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_172_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_173_, 0, v_repo_169_);
v___x_174_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_175_ = 1;
v___x_176_ = 0;
v___x_177_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_177_, 0, v___x_171_);
lean_ctor_set(v___x_177_, 1, v___x_172_);
lean_ctor_set(v___x_177_, 2, v_args_168_);
lean_ctor_set(v___x_177_, 3, v___x_173_);
lean_ctor_set(v___x_177_, 4, v___x_174_);
lean_ctor_set_uint8(v___x_177_, sizeof(void*)*5, v___x_175_);
lean_ctor_set_uint8(v___x_177_, sizeof(void*)*5 + 1, v___x_176_);
v___x_178_ = l_Lake_testProc(v___x_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_testGit___boxed(lean_object* v_args_179_, lean_object* v_repo_180_, lean_object* v_a_181_){
_start:
{
uint8_t v_res_182_; lean_object* v_r_183_; 
v_res_182_ = l_Lake_GitRepo_testGit(v_args_179_, v_repo_180_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__0(uint8_t v___x_184_, uint8_t v___x_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
if (v___x_184_ == 0)
{
uint8_t v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_189_ = 1;
v___x_190_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_190_, 0, v___y_186_);
lean_ctor_set_uint8(v___x_190_, sizeof(void*)*1, v___x_189_);
v___x_191_ = lean_box(0);
v___x_192_ = lean_array_push(v___y_187_, v___x_190_);
v___x_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_191_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
return v___x_193_;
}
else
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_194_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_194_, 0, v___y_186_);
lean_ctor_set_uint8(v___x_194_, sizeof(void*)*1, v___x_185_);
v___x_195_ = lean_box(0);
v___x_196_ = lean_array_push(v___y_187_, v___x_194_);
v___x_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_195_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
return v___x_197_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__0___boxed(lean_object* v___x_198_, lean_object* v___x_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
uint8_t v___x_2102__boxed_203_; uint8_t v___x_2103__boxed_204_; lean_object* v_res_205_; 
v___x_2102__boxed_203_ = lean_unbox(v___x_198_);
v___x_2103__boxed_204_ = lean_unbox(v___x_199_);
v_res_205_ = l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__0(v___x_2102__boxed_203_, v___x_2103__boxed_204_, v___y_200_, v___y_201_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1(lean_object* v_stderr_207_, lean_object* v___x_208_, lean_object* v___y_209_, lean_object* v_____r_210_, lean_object* v___y_211_){
_start:
{
lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_213_ = lean_string_utf8_byte_size(v_stderr_207_);
v___x_214_ = lean_nat_dec_eq(v___x_213_, v___x_208_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_215_ = ((lean_object*)(l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1___closed__0));
v___x_216_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_216_, 0, v_stderr_207_);
lean_ctor_set(v___x_216_, 1, v___x_208_);
lean_ctor_set(v___x_216_, 2, v___x_213_);
v___x_217_ = l_String_Slice_trimAscii(v___x_216_);
v___x_218_ = l_String_Slice_toString(v___x_217_);
lean_dec_ref(v___x_217_);
v___x_219_ = lean_string_append(v___x_215_, v___x_218_);
lean_dec_ref(v___x_218_);
v___x_220_ = lean_apply_3(v___y_209_, v___x_219_, v___y_211_, lean_box(0));
return v___x_220_;
}
else
{
lean_object* v___x_221_; lean_object* v___x_222_; 
lean_dec_ref(v___y_209_);
lean_dec(v___x_208_);
lean_dec_ref(v_stderr_207_);
v___x_221_ = lean_box(0);
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v___y_211_);
return v___x_222_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1___boxed(lean_object* v_stderr_223_, lean_object* v___x_224_, lean_object* v___y_225_, lean_object* v_____r_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1(v_stderr_223_, v___x_224_, v___y_225_, v_____r_226_, v___y_227_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit(lean_object* v_args_232_, lean_object* v_repo_233_, lean_object* v_a_234_){
_start:
{
lean_object* v_a_237_; lean_object* v_a_238_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; uint8_t v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_240_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_241_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_242_, 0, v_repo_233_);
v___x_243_ = lean_unsigned_to_nat(0u);
v___x_244_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_245_ = 1;
v___x_246_ = 0;
v___x_247_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_247_, 0, v___x_240_);
lean_ctor_set(v___x_247_, 1, v___x_241_);
lean_ctor_set(v___x_247_, 2, v_args_232_);
lean_ctor_set(v___x_247_, 3, v___x_242_);
lean_ctor_set(v___x_247_, 4, v___x_244_);
lean_ctor_set_uint8(v___x_247_, sizeof(void*)*5, v___x_245_);
lean_ctor_set_uint8(v___x_247_, sizeof(void*)*5 + 1, v___x_246_);
v___x_248_ = lean_box(0);
v___x_249_ = lean_array_get_size(v_a_234_);
lean_inc_ref(v___x_247_);
v___x_250_ = l_Lake_mkCmdLog(v___x_247_);
v___x_251_ = 0;
v___x_252_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_252_, 0, v___x_250_);
lean_ctor_set_uint8(v___x_252_, sizeof(void*)*1, v___x_251_);
v___x_253_ = lean_array_push(v_a_234_, v___x_252_);
v___x_254_ = l_IO_Process_output(v___x_247_, v___x_248_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; uint32_t v_exitCode_256_; lean_object* v_stdout_257_; lean_object* v_stderr_258_; uint32_t v___x_259_; uint8_t v___x_260_; lean_object* v___y_262_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___y_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_a_255_);
lean_dec_ref_known(v___x_254_, 1);
v_exitCode_256_ = lean_ctor_get_uint32(v_a_255_, sizeof(void*)*2);
v_stdout_257_ = lean_ctor_get(v_a_255_, 0);
lean_inc_ref(v_stdout_257_);
v_stderr_258_ = lean_ctor_get(v_a_255_, 1);
lean_inc_ref(v_stderr_258_);
lean_dec(v_a_255_);
v___x_259_ = 0;
v___x_260_ = lean_uint32_dec_eq(v_exitCode_256_, v___x_259_);
v___x_275_ = lean_box(v___x_260_);
v___x_276_ = lean_box(v___x_251_);
v___y_277_ = lean_alloc_closure((void*)(l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__0___boxed), 5, 2);
lean_closure_set(v___y_277_, 0, v___x_275_);
lean_closure_set(v___y_277_, 1, v___x_276_);
v___x_278_ = lean_string_utf8_byte_size(v_stdout_257_);
v___x_279_ = lean_nat_dec_eq(v___x_278_, v___x_243_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v_a_286_; lean_object* v_a_287_; lean_object* v___x_288_; 
v___x_280_ = ((lean_object*)(l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___closed__0));
v___x_281_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_281_, 0, v_stdout_257_);
lean_ctor_set(v___x_281_, 1, v___x_243_);
lean_ctor_set(v___x_281_, 2, v___x_278_);
v___x_282_ = l_String_Slice_trimAscii(v___x_281_);
v___x_283_ = l_String_Slice_toString(v___x_282_);
lean_dec_ref(v___x_282_);
v___x_284_ = lean_string_append(v___x_280_, v___x_283_);
lean_dec_ref(v___x_283_);
v___x_285_ = l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__0(v___x_260_, v___x_251_, v___x_284_, v___x_253_);
v_a_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc(v_a_286_);
v_a_287_ = lean_ctor_get(v___x_285_, 1);
lean_inc(v_a_287_);
lean_dec_ref(v___x_285_);
v___x_288_ = l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1(v_stderr_258_, v___x_243_, v___y_277_, v_a_286_, v_a_287_);
v___y_262_ = v___x_288_;
goto v___jp_261_;
}
else
{
lean_object* v___x_289_; lean_object* v___x_290_; 
lean_dec_ref(v_stdout_257_);
v___x_289_ = lean_box(0);
v___x_290_ = l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1(v_stderr_258_, v___x_243_, v___y_277_, v___x_289_, v___x_253_);
v___y_262_ = v___x_290_;
goto v___jp_261_;
}
v___jp_261_:
{
if (lean_obj_tag(v___y_262_) == 0)
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_271_; 
v_a_263_ = lean_ctor_get(v___y_262_, 1);
v_isSharedCheck_271_ = !lean_is_exclusive(v___y_262_);
if (v_isSharedCheck_271_ == 0)
{
lean_object* v_unused_272_; 
v_unused_272_ = lean_ctor_get(v___y_262_, 0);
lean_dec(v_unused_272_);
v___x_265_ = v___y_262_;
v_isShared_266_ = v_isSharedCheck_271_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___y_262_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_271_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_267_ = lean_box(v___x_260_);
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 0, v___x_267_);
v___x_269_ = v___x_265_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_267_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v_a_263_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
else
{
lean_object* v_a_273_; lean_object* v_a_274_; 
v_a_273_ = lean_ctor_get(v___y_262_, 0);
lean_inc(v_a_273_);
v_a_274_ = lean_ctor_get(v___y_262_, 1);
lean_inc(v_a_274_);
lean_dec_ref_known(v___y_262_, 2);
v_a_237_ = v_a_273_;
v_a_238_ = v_a_274_;
goto v___jp_236_;
}
}
}
else
{
lean_object* v_a_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v_a_291_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_a_291_);
lean_dec_ref_known(v___x_254_, 1);
v___x_292_ = ((lean_object*)(l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___closed__1));
v___x_293_ = lean_io_error_to_string(v_a_291_);
v___x_294_ = lean_string_append(v___x_292_, v___x_293_);
lean_dec_ref(v___x_293_);
v___x_295_ = 3;
v___x_296_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_296_, 0, v___x_294_);
lean_ctor_set_uint8(v___x_296_, sizeof(void*)*1, v___x_295_);
v___x_297_ = lean_array_push(v___x_253_, v___x_296_);
v___x_298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_249_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
return v___x_298_;
}
v___jp_236_:
{
lean_object* v___x_239_; 
v___x_239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_239_, 0, v_a_237_);
lean_ctor_set(v___x_239_, 1, v_a_238_);
return v___x_239_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___boxed(lean_object* v_args_299_, lean_object* v_repo_300_, lean_object* v_a_301_, lean_object* v_a_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit(v_args_299_, v_repo_300_, v_a_301_);
return v_res_303_;
}
}
static lean_object* _init_l_Lake_GitRepo_clone___closed__1(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_305_ = ((lean_object*)(l_Lake_GitRepo_clone___closed__0));
v___x_306_ = lean_unsigned_to_nat(3u);
v___x_307_ = lean_mk_empty_array_with_capacity(v___x_306_);
v___x_308_ = lean_array_push(v___x_307_, v___x_305_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone(lean_object* v_url_309_, lean_object* v_repo_310_, lean_object* v_a_311_){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; uint8_t v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_313_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_314_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_315_ = lean_obj_once(&l_Lake_GitRepo_clone___closed__1, &l_Lake_GitRepo_clone___closed__1_once, _init_l_Lake_GitRepo_clone___closed__1);
v___x_316_ = lean_array_push(v___x_315_, v_url_309_);
v___x_317_ = lean_array_push(v___x_316_, v_repo_310_);
v___x_318_ = lean_box(0);
v___x_319_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_320_ = 1;
v___x_321_ = 0;
v___x_322_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_322_, 0, v___x_313_);
lean_ctor_set(v___x_322_, 1, v___x_314_);
lean_ctor_set(v___x_322_, 2, v___x_317_);
lean_ctor_set(v___x_322_, 3, v___x_318_);
lean_ctor_set(v___x_322_, 4, v___x_319_);
lean_ctor_set_uint8(v___x_322_, sizeof(void*)*5, v___x_320_);
lean_ctor_set_uint8(v___x_322_, sizeof(void*)*5 + 1, v___x_321_);
v___x_323_ = l_Lake_proc(v___x_322_, v___x_320_, v___x_318_, v_a_311_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone___boxed(lean_object* v_url_324_, lean_object* v_repo_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lake_GitRepo_clone(v_url_324_, v_repo_325_, v_a_326_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit(lean_object* v_repo_337_, lean_object* v_a_338_){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; uint8_t v___x_345_; uint8_t v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_340_ = ((lean_object*)(l_Lake_GitRepo_quietInit___closed__2));
v___x_341_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_342_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_343_, 0, v_repo_337_);
v___x_344_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_345_ = 1;
v___x_346_ = 0;
v___x_347_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_347_, 0, v___x_341_);
lean_ctor_set(v___x_347_, 1, v___x_342_);
lean_ctor_set(v___x_347_, 2, v___x_340_);
lean_ctor_set(v___x_347_, 3, v___x_343_);
lean_ctor_set(v___x_347_, 4, v___x_344_);
lean_ctor_set_uint8(v___x_347_, sizeof(void*)*5, v___x_345_);
lean_ctor_set_uint8(v___x_347_, sizeof(void*)*5 + 1, v___x_346_);
v___x_348_ = lean_box(0);
v___x_349_ = l_Lake_proc(v___x_347_, v___x_345_, v___x_348_, v_a_338_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit___boxed(lean_object* v_repo_350_, lean_object* v_a_351_, lean_object* v_a_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lake_GitRepo_quietInit(v_repo_350_, v_a_351_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_bareInit(lean_object* v_repo_363_, lean_object* v_a_364_){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; uint8_t v___x_371_; uint8_t v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_366_ = ((lean_object*)(l_Lake_GitRepo_bareInit___closed__1));
v___x_367_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_368_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_369_, 0, v_repo_363_);
v___x_370_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_371_ = 1;
v___x_372_ = 0;
v___x_373_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_373_, 0, v___x_367_);
lean_ctor_set(v___x_373_, 1, v___x_368_);
lean_ctor_set(v___x_373_, 2, v___x_366_);
lean_ctor_set(v___x_373_, 3, v___x_369_);
lean_ctor_set(v___x_373_, 4, v___x_370_);
lean_ctor_set_uint8(v___x_373_, sizeof(void*)*5, v___x_371_);
lean_ctor_set_uint8(v___x_373_, sizeof(void*)*5 + 1, v___x_372_);
v___x_374_ = lean_box(0);
v___x_375_ = l_Lake_proc(v___x_373_, v___x_371_, v___x_374_, v_a_364_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_bareInit___boxed(lean_object* v_repo_376_, lean_object* v_a_377_, lean_object* v_a_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lake_GitRepo_bareInit(v_repo_376_, v_a_377_);
return v_res_379_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_insideWorkTree(lean_object* v_repo_388_){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; uint8_t v___x_395_; uint8_t v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
v___x_390_ = ((lean_object*)(l_Lake_GitRepo_insideWorkTree___closed__2));
v___x_391_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_392_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_393_, 0, v_repo_388_);
v___x_394_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_395_ = 1;
v___x_396_ = 0;
v___x_397_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_397_, 0, v___x_391_);
lean_ctor_set(v___x_397_, 1, v___x_392_);
lean_ctor_set(v___x_397_, 2, v___x_390_);
lean_ctor_set(v___x_397_, 3, v___x_393_);
lean_ctor_set(v___x_397_, 4, v___x_394_);
lean_ctor_set_uint8(v___x_397_, sizeof(void*)*5, v___x_395_);
lean_ctor_set_uint8(v___x_397_, sizeof(void*)*5 + 1, v___x_396_);
v___x_398_ = l_Lake_testProc(v___x_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_insideWorkTree___boxed(lean_object* v_repo_399_, lean_object* v_a_400_){
_start:
{
uint8_t v_res_401_; lean_object* v_r_402_; 
v_res_401_ = l_Lake_GitRepo_insideWorkTree(v_repo_399_);
v_r_402_ = lean_box(v_res_401_);
return v_r_402_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__3(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_406_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__0));
v___x_407_ = lean_unsigned_to_nat(4u);
v___x_408_ = lean_mk_empty_array_with_capacity(v___x_407_);
v___x_409_ = lean_array_push(v___x_408_, v___x_406_);
return v___x_409_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__4(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_410_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__1));
v___x_411_ = lean_obj_once(&l_Lake_GitRepo_fetch___closed__3, &l_Lake_GitRepo_fetch___closed__3_once, _init_l_Lake_GitRepo_fetch___closed__3);
v___x_412_ = lean_array_push(v___x_411_, v___x_410_);
return v___x_412_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__5(void){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_413_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__2));
v___x_414_ = lean_obj_once(&l_Lake_GitRepo_fetch___closed__4, &l_Lake_GitRepo_fetch___closed__4_once, _init_l_Lake_GitRepo_fetch___closed__4);
v___x_415_ = lean_array_push(v___x_414_, v___x_413_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch(lean_object* v_repo_416_, lean_object* v_remote_417_, lean_object* v_a_418_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; uint8_t v___x_426_; uint8_t v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_420_ = lean_obj_once(&l_Lake_GitRepo_fetch___closed__5, &l_Lake_GitRepo_fetch___closed__5_once, _init_l_Lake_GitRepo_fetch___closed__5);
v___x_421_ = lean_array_push(v___x_420_, v_remote_417_);
v___x_422_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_423_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_424_, 0, v_repo_416_);
v___x_425_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_426_ = 1;
v___x_427_ = 0;
v___x_428_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_428_, 0, v___x_422_);
lean_ctor_set(v___x_428_, 1, v___x_423_);
lean_ctor_set(v___x_428_, 2, v___x_421_);
lean_ctor_set(v___x_428_, 3, v___x_424_);
lean_ctor_set(v___x_428_, 4, v___x_425_);
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*5, v___x_426_);
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*5 + 1, v___x_427_);
v___x_429_ = lean_box(0);
v___x_430_ = l_Lake_proc(v___x_428_, v___x_426_, v___x_429_, v_a_418_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch___boxed(lean_object* v_repo_431_, lean_object* v_remote_432_, lean_object* v_a_433_, lean_object* v_a_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lake_GitRepo_fetch(v_repo_431_, v_remote_432_, v_a_433_);
return v_res_435_;
}
}
static lean_object* _init_l_Lake_GitRepo_addWorktreeDetach___closed__3(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_439_ = ((lean_object*)(l_Lake_GitRepo_addWorktreeDetach___closed__0));
v___x_440_ = lean_unsigned_to_nat(5u);
v___x_441_ = lean_mk_empty_array_with_capacity(v___x_440_);
v___x_442_ = lean_array_push(v___x_441_, v___x_439_);
return v___x_442_;
}
}
static lean_object* _init_l_Lake_GitRepo_addWorktreeDetach___closed__4(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = ((lean_object*)(l_Lake_GitRepo_addWorktreeDetach___closed__1));
v___x_444_ = lean_obj_once(&l_Lake_GitRepo_addWorktreeDetach___closed__3, &l_Lake_GitRepo_addWorktreeDetach___closed__3_once, _init_l_Lake_GitRepo_addWorktreeDetach___closed__3);
v___x_445_ = lean_array_push(v___x_444_, v___x_443_);
return v___x_445_;
}
}
static lean_object* _init_l_Lake_GitRepo_addWorktreeDetach___closed__5(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_446_ = ((lean_object*)(l_Lake_GitRepo_addWorktreeDetach___closed__2));
v___x_447_ = lean_obj_once(&l_Lake_GitRepo_addWorktreeDetach___closed__4, &l_Lake_GitRepo_addWorktreeDetach___closed__4_once, _init_l_Lake_GitRepo_addWorktreeDetach___closed__4);
v___x_448_ = lean_array_push(v___x_447_, v___x_446_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_addWorktreeDetach(lean_object* v_path_449_, lean_object* v_rev_450_, lean_object* v_repo_451_, lean_object* v_a_452_){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; uint8_t v___x_461_; uint8_t v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_454_ = lean_obj_once(&l_Lake_GitRepo_addWorktreeDetach___closed__5, &l_Lake_GitRepo_addWorktreeDetach___closed__5_once, _init_l_Lake_GitRepo_addWorktreeDetach___closed__5);
v___x_455_ = lean_array_push(v___x_454_, v_path_449_);
v___x_456_ = lean_array_push(v___x_455_, v_rev_450_);
v___x_457_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_458_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_459_, 0, v_repo_451_);
v___x_460_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_461_ = 1;
v___x_462_ = 0;
v___x_463_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_463_, 0, v___x_457_);
lean_ctor_set(v___x_463_, 1, v___x_458_);
lean_ctor_set(v___x_463_, 2, v___x_456_);
lean_ctor_set(v___x_463_, 3, v___x_459_);
lean_ctor_set(v___x_463_, 4, v___x_460_);
lean_ctor_set_uint8(v___x_463_, sizeof(void*)*5, v___x_461_);
lean_ctor_set_uint8(v___x_463_, sizeof(void*)*5 + 1, v___x_462_);
v___x_464_ = lean_box(0);
v___x_465_ = l_Lake_proc(v___x_463_, v___x_461_, v___x_464_, v_a_452_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_addWorktreeDetach___boxed(lean_object* v_path_466_, lean_object* v_rev_467_, lean_object* v_repo_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lake_GitRepo_addWorktreeDetach(v_path_466_, v_rev_467_, v_repo_468_, v_a_469_);
return v_res_471_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutBranch___closed__2(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_474_ = ((lean_object*)(l_Lake_GitRepo_checkoutBranch___closed__0));
v___x_475_ = lean_unsigned_to_nat(3u);
v___x_476_ = lean_mk_empty_array_with_capacity(v___x_475_);
v___x_477_ = lean_array_push(v___x_476_, v___x_474_);
return v___x_477_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutBranch___closed__3(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = ((lean_object*)(l_Lake_GitRepo_checkoutBranch___closed__1));
v___x_479_ = lean_obj_once(&l_Lake_GitRepo_checkoutBranch___closed__2, &l_Lake_GitRepo_checkoutBranch___closed__2_once, _init_l_Lake_GitRepo_checkoutBranch___closed__2);
v___x_480_ = lean_array_push(v___x_479_, v___x_478_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch(lean_object* v_branch_481_, lean_object* v_repo_482_, lean_object* v_a_483_){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; uint8_t v___x_491_; uint8_t v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_485_ = lean_obj_once(&l_Lake_GitRepo_checkoutBranch___closed__3, &l_Lake_GitRepo_checkoutBranch___closed__3_once, _init_l_Lake_GitRepo_checkoutBranch___closed__3);
v___x_486_ = lean_array_push(v___x_485_, v_branch_481_);
v___x_487_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_488_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_489_, 0, v_repo_482_);
v___x_490_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_491_ = 1;
v___x_492_ = 0;
v___x_493_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_493_, 0, v___x_487_);
lean_ctor_set(v___x_493_, 1, v___x_488_);
lean_ctor_set(v___x_493_, 2, v___x_486_);
lean_ctor_set(v___x_493_, 3, v___x_489_);
lean_ctor_set(v___x_493_, 4, v___x_490_);
lean_ctor_set_uint8(v___x_493_, sizeof(void*)*5, v___x_491_);
lean_ctor_set_uint8(v___x_493_, sizeof(void*)*5 + 1, v___x_492_);
v___x_494_ = lean_box(0);
v___x_495_ = l_Lake_proc(v___x_493_, v___x_491_, v___x_494_, v_a_483_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch___boxed(lean_object* v_branch_496_, lean_object* v_repo_497_, lean_object* v_a_498_, lean_object* v_a_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lake_GitRepo_checkoutBranch(v_branch_496_, v_repo_497_, v_a_498_);
return v_res_500_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutDetach___closed__1(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_502_ = ((lean_object*)(l_Lake_GitRepo_checkoutBranch___closed__0));
v___x_503_ = lean_unsigned_to_nat(4u);
v___x_504_ = lean_mk_empty_array_with_capacity(v___x_503_);
v___x_505_ = lean_array_push(v___x_504_, v___x_502_);
return v___x_505_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutDetach___closed__2(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_506_ = ((lean_object*)(l_Lake_GitRepo_addWorktreeDetach___closed__2));
v___x_507_ = lean_obj_once(&l_Lake_GitRepo_checkoutDetach___closed__1, &l_Lake_GitRepo_checkoutDetach___closed__1_once, _init_l_Lake_GitRepo_checkoutDetach___closed__1);
v___x_508_ = lean_array_push(v___x_507_, v___x_506_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach(lean_object* v_hash_509_, lean_object* v_repo_510_, lean_object* v_a_511_){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; uint8_t v___x_521_; uint8_t v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_513_ = ((lean_object*)(l_Lake_GitRepo_checkoutDetach___closed__0));
v___x_514_ = lean_obj_once(&l_Lake_GitRepo_checkoutDetach___closed__2, &l_Lake_GitRepo_checkoutDetach___closed__2_once, _init_l_Lake_GitRepo_checkoutDetach___closed__2);
v___x_515_ = lean_array_push(v___x_514_, v_hash_509_);
v___x_516_ = lean_array_push(v___x_515_, v___x_513_);
v___x_517_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_518_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_519_, 0, v_repo_510_);
v___x_520_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_521_ = 1;
v___x_522_ = 0;
v___x_523_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_523_, 0, v___x_517_);
lean_ctor_set(v___x_523_, 1, v___x_518_);
lean_ctor_set(v___x_523_, 2, v___x_516_);
lean_ctor_set(v___x_523_, 3, v___x_519_);
lean_ctor_set(v___x_523_, 4, v___x_520_);
lean_ctor_set_uint8(v___x_523_, sizeof(void*)*5, v___x_521_);
lean_ctor_set_uint8(v___x_523_, sizeof(void*)*5 + 1, v___x_522_);
v___x_524_ = lean_box(0);
v___x_525_ = l_Lake_proc(v___x_523_, v___x_521_, v___x_524_, v_a_511_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach___boxed(lean_object* v_hash_526_, lean_object* v_repo_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lake_GitRepo_checkoutDetach(v_hash_526_, v_repo_527_, v_a_528_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_gcAuto(lean_object* v_repo_539_, lean_object* v_a_540_){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; uint8_t v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_542_ = ((lean_object*)(l_Lake_GitRepo_gcAuto___closed__2));
v___x_543_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_544_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_545_, 0, v_repo_539_);
v___x_546_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_547_ = 1;
v___x_548_ = 0;
v___x_549_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_549_, 0, v___x_543_);
lean_ctor_set(v___x_549_, 1, v___x_544_);
lean_ctor_set(v___x_549_, 2, v___x_542_);
lean_ctor_set(v___x_549_, 3, v___x_545_);
lean_ctor_set(v___x_549_, 4, v___x_546_);
lean_ctor_set_uint8(v___x_549_, sizeof(void*)*5, v___x_547_);
lean_ctor_set_uint8(v___x_549_, sizeof(void*)*5 + 1, v___x_548_);
v___x_550_ = lean_box(0);
v___x_551_ = l_Lake_proc(v___x_549_, v___x_547_, v___x_550_, v_a_540_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_gcAuto___boxed(lean_object* v_repo_552_, lean_object* v_a_553_, lean_object* v_a_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Lake_GitRepo_gcAuto(v_repo_552_, v_a_553_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clean(lean_object* v_repo_564_, lean_object* v_a_565_){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; uint8_t v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_567_ = ((lean_object*)(l_Lake_GitRepo_clean___closed__2));
v___x_568_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_569_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_570_, 0, v_repo_564_);
v___x_571_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_572_ = 1;
v___x_573_ = 0;
v___x_574_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_574_, 0, v___x_568_);
lean_ctor_set(v___x_574_, 1, v___x_569_);
lean_ctor_set(v___x_574_, 2, v___x_567_);
lean_ctor_set(v___x_574_, 3, v___x_570_);
lean_ctor_set(v___x_574_, 4, v___x_571_);
lean_ctor_set_uint8(v___x_574_, sizeof(void*)*5, v___x_572_);
lean_ctor_set_uint8(v___x_574_, sizeof(void*)*5 + 1, v___x_573_);
v___x_575_ = lean_box(0);
v___x_576_ = l_Lake_proc(v___x_574_, v___x_572_, v___x_575_, v_a_565_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clean___boxed(lean_object* v_repo_577_, lean_object* v_a_578_, lean_object* v_a_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lake_GitRepo_clean(v_repo_577_, v_a_578_);
return v_res_580_;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__2(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_583_ = ((lean_object*)(l_Lake_GitRepo_insideWorkTree___closed__0));
v___x_584_ = lean_unsigned_to_nat(4u);
v___x_585_ = lean_mk_empty_array_with_capacity(v___x_584_);
v___x_586_ = lean_array_push(v___x_585_, v___x_583_);
return v___x_586_;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__3(void){
_start:
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_587_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__0));
v___x_588_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__2, &l_Lake_GitRepo_resolveRevision_x3f___closed__2_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__2);
v___x_589_ = lean_array_push(v___x_588_, v___x_587_);
return v___x_589_;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_590_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__1));
v___x_591_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__3, &l_Lake_GitRepo_resolveRevision_x3f___closed__3_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__3);
v___x_592_ = lean_array_push(v___x_591_, v___x_590_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object* v_rev_593_, lean_object* v_repo_594_){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; uint8_t v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_596_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__4, &l_Lake_GitRepo_resolveRevision_x3f___closed__4_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4);
v___x_597_ = lean_array_push(v___x_596_, v_rev_593_);
v___x_598_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_599_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_600_, 0, v_repo_594_);
v___x_601_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_602_ = 1;
v___x_603_ = 0;
v___x_604_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_604_, 0, v___x_598_);
lean_ctor_set(v___x_604_, 1, v___x_599_);
lean_ctor_set(v___x_604_, 2, v___x_597_);
lean_ctor_set(v___x_604_, 3, v___x_600_);
lean_ctor_set(v___x_604_, 4, v___x_601_);
lean_ctor_set_uint8(v___x_604_, sizeof(void*)*5, v___x_602_);
lean_ctor_set_uint8(v___x_604_, sizeof(void*)*5 + 1, v___x_603_);
v___x_605_ = l_Lake_captureProc_x3f(v___x_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f___boxed(lean_object* v_rev_606_, lean_object* v_repo_607_, lean_object* v_a_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_606_, v_repo_607_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findCommit_x3f(lean_object* v_rev_611_, lean_object* v_repo_612_){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; uint8_t v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_614_ = ((lean_object*)(l_Lake_GitRepo_findCommit_x3f___closed__0));
v___x_615_ = lean_string_append(v_rev_611_, v___x_614_);
v___x_616_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__4, &l_Lake_GitRepo_resolveRevision_x3f___closed__4_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4);
v___x_617_ = lean_array_push(v___x_616_, v___x_615_);
v___x_618_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_619_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_620_, 0, v_repo_612_);
v___x_621_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_622_ = 1;
v___x_623_ = 0;
v___x_624_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_624_, 0, v___x_618_);
lean_ctor_set(v___x_624_, 1, v___x_619_);
lean_ctor_set(v___x_624_, 2, v___x_617_);
lean_ctor_set(v___x_624_, 3, v___x_620_);
lean_ctor_set(v___x_624_, 4, v___x_621_);
lean_ctor_set_uint8(v___x_624_, sizeof(void*)*5, v___x_622_);
lean_ctor_set_uint8(v___x_624_, sizeof(void*)*5 + 1, v___x_623_);
v___x_625_ = l_Lake_captureProc_x3f(v___x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findCommit_x3f___boxed(lean_object* v_rev_626_, lean_object* v_repo_627_, lean_object* v_a_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l_Lake_GitRepo_findCommit_x3f(v_rev_626_, v_repo_627_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision(lean_object* v_rev_632_, lean_object* v_repo_633_, lean_object* v_a_634_){
_start:
{
uint8_t v___x_636_; 
v___x_636_ = l_Lake_GitRev_isFullSha1(v_rev_632_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; 
lean_inc_ref(v_repo_633_);
lean_inc_ref(v_rev_632_);
v___x_637_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_632_, v_repo_633_);
if (lean_obj_tag(v___x_637_) == 1)
{
lean_object* v_val_638_; lean_object* v___x_639_; 
lean_dec_ref(v_repo_633_);
lean_dec_ref(v_rev_632_);
v_val_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_val_638_);
lean_dec_ref_known(v___x_637_, 1);
v___x_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_639_, 0, v_val_638_);
lean_ctor_set(v___x_639_, 1, v_a_634_);
return v___x_639_;
}
else
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; uint8_t v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
lean_dec(v___x_637_);
v___x_640_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__0));
v___x_641_ = lean_string_append(v_repo_633_, v___x_640_);
v___x_642_ = lean_string_append(v___x_641_, v_rev_632_);
lean_dec_ref(v_rev_632_);
v___x_643_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__1));
v___x_644_ = lean_string_append(v___x_642_, v___x_643_);
v___x_645_ = 3;
v___x_646_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_646_, 0, v___x_644_);
lean_ctor_set_uint8(v___x_646_, sizeof(void*)*1, v___x_645_);
v___x_647_ = lean_array_get_size(v_a_634_);
v___x_648_ = lean_array_push(v_a_634_, v___x_646_);
v___x_649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_647_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
return v___x_649_;
}
}
else
{
lean_object* v___x_650_; 
lean_dec_ref(v_repo_633_);
v___x_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_650_, 0, v_rev_632_);
lean_ctor_set(v___x_650_, 1, v_a_634_);
return v___x_650_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision___boxed(lean_object* v_rev_651_, lean_object* v_repo_652_, lean_object* v_a_653_, lean_object* v_a_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lake_GitRepo_resolveRevision(v_rev_651_, v_repo_652_, v_a_653_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f(lean_object* v_repo_656_){
_start:
{
lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_658_ = ((lean_object*)(l_Lake_GitRev_head___closed__0));
v___x_659_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_658_, v_repo_656_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f___boxed(lean_object* v_repo_660_, lean_object* v_a_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lake_GitRepo_getHeadRevision_x3f(v_repo_660_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision(lean_object* v_repo_664_, lean_object* v_a_665_){
_start:
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = ((lean_object*)(l_Lake_GitRev_head___closed__0));
lean_inc_ref(v_repo_664_);
v___x_668_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_667_, v_repo_664_);
if (lean_obj_tag(v___x_668_) == 1)
{
lean_object* v_val_669_; lean_object* v___x_670_; 
lean_dec_ref(v_repo_664_);
v_val_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_val_669_);
lean_dec_ref_known(v___x_668_, 1);
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v_val_669_);
lean_ctor_set(v___x_670_, 1, v_a_665_);
return v___x_670_;
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
lean_dec(v___x_668_);
v___x_671_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevision___closed__0));
v___x_672_ = lean_string_append(v_repo_664_, v___x_671_);
v___x_673_ = 3;
v___x_674_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_674_, 0, v___x_672_);
lean_ctor_set_uint8(v___x_674_, sizeof(void*)*1, v___x_673_);
v___x_675_ = lean_array_get_size(v_a_665_);
v___x_676_ = lean_array_push(v_a_665_, v___x_674_);
v___x_677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_675_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
return v___x_677_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision___boxed(lean_object* v_repo_678_, lean_object* v_a_679_, lean_object* v_a_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lake_GitRepo_getHeadRevision(v_repo_678_, v_a_679_);
return v_res_681_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetchRevision_x3f___closed__1(void){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_683_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__0));
v___x_684_ = lean_unsigned_to_nat(6u);
v___x_685_ = lean_mk_empty_array_with_capacity(v___x_684_);
v___x_686_ = lean_array_push(v___x_685_, v___x_683_);
return v___x_686_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetchRevision_x3f___closed__2(void){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_687_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__1));
v___x_688_ = lean_obj_once(&l_Lake_GitRepo_fetchRevision_x3f___closed__1, &l_Lake_GitRepo_fetchRevision_x3f___closed__1_once, _init_l_Lake_GitRepo_fetchRevision_x3f___closed__1);
v___x_689_ = lean_array_push(v___x_688_, v___x_687_);
return v___x_689_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetchRevision_x3f___closed__3(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_690_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__2));
v___x_691_ = lean_obj_once(&l_Lake_GitRepo_fetchRevision_x3f___closed__2, &l_Lake_GitRepo_fetchRevision_x3f___closed__2_once, _init_l_Lake_GitRepo_fetchRevision_x3f___closed__2);
v___x_692_ = lean_array_push(v___x_691_, v___x_690_);
return v___x_692_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetchRevision_x3f___closed__4(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_693_ = ((lean_object*)(l_Lake_GitRepo_fetchRevision_x3f___closed__0));
v___x_694_ = lean_obj_once(&l_Lake_GitRepo_fetchRevision_x3f___closed__3, &l_Lake_GitRepo_fetchRevision_x3f___closed__3_once, _init_l_Lake_GitRepo_fetchRevision_x3f___closed__3);
v___x_695_ = lean_array_push(v___x_694_, v___x_693_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetchRevision_x3f(lean_object* v_repo_697_, lean_object* v_remote_698_, lean_object* v_rev_699_, lean_object* v_a_700_){
_start:
{
lean_object* v_a_703_; lean_object* v_a_704_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v_args_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; uint8_t v___x_714_; uint8_t v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_706_ = lean_obj_once(&l_Lake_GitRepo_fetchRevision_x3f___closed__4, &l_Lake_GitRepo_fetchRevision_x3f___closed__4_once, _init_l_Lake_GitRepo_fetchRevision_x3f___closed__4);
v___x_707_ = lean_array_push(v___x_706_, v_remote_698_);
v_args_708_ = lean_array_push(v___x_707_, v_rev_699_);
v___x_709_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_710_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
lean_inc_ref(v_repo_697_);
v___x_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_711_, 0, v_repo_697_);
v___x_712_ = lean_unsigned_to_nat(0u);
v___x_713_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_714_ = 1;
v___x_715_ = 0;
v___x_716_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_716_, 0, v___x_709_);
lean_ctor_set(v___x_716_, 1, v___x_710_);
lean_ctor_set(v___x_716_, 2, v_args_708_);
lean_ctor_set(v___x_716_, 3, v___x_711_);
lean_ctor_set(v___x_716_, 4, v___x_713_);
lean_ctor_set_uint8(v___x_716_, sizeof(void*)*5, v___x_714_);
lean_ctor_set_uint8(v___x_716_, sizeof(void*)*5 + 1, v___x_715_);
v___x_717_ = lean_box(0);
v___x_718_ = lean_array_get_size(v_a_700_);
lean_inc_ref(v___x_716_);
v___x_719_ = l_Lake_mkCmdLog(v___x_716_);
v___x_720_ = 0;
v___x_721_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_721_, 0, v___x_719_);
lean_ctor_set_uint8(v___x_721_, sizeof(void*)*1, v___x_720_);
v___x_722_ = lean_array_push(v_a_700_, v___x_721_);
v___x_723_ = l_IO_Process_output(v___x_716_, v___x_717_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; uint32_t v_exitCode_725_; lean_object* v_stdout_726_; lean_object* v_stderr_727_; uint32_t v___x_728_; uint8_t v___x_729_; lean_object* v___y_731_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___y_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_724_);
lean_dec_ref_known(v___x_723_, 1);
v_exitCode_725_ = lean_ctor_get_uint32(v_a_724_, sizeof(void*)*2);
v_stdout_726_ = lean_ctor_get(v_a_724_, 0);
lean_inc_ref(v_stdout_726_);
v_stderr_727_ = lean_ctor_get(v_a_724_, 1);
lean_inc_ref(v_stderr_727_);
lean_dec(v_a_724_);
v___x_728_ = 0;
v___x_729_ = lean_uint32_dec_eq(v_exitCode_725_, v___x_728_);
v___x_763_ = lean_box(v___x_729_);
v___x_764_ = lean_box(v___x_720_);
v___y_765_ = lean_alloc_closure((void*)(l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__0___boxed), 5, 2);
lean_closure_set(v___y_765_, 0, v___x_763_);
lean_closure_set(v___y_765_, 1, v___x_764_);
v___x_766_ = lean_string_utf8_byte_size(v_stdout_726_);
v___x_767_ = lean_nat_dec_eq(v___x_766_, v___x_712_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v_a_774_; lean_object* v_a_775_; lean_object* v___x_776_; 
v___x_768_ = ((lean_object*)(l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___closed__0));
v___x_769_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_769_, 0, v_stdout_726_);
lean_ctor_set(v___x_769_, 1, v___x_712_);
lean_ctor_set(v___x_769_, 2, v___x_766_);
v___x_770_ = l_String_Slice_trimAscii(v___x_769_);
v___x_771_ = l_String_Slice_toString(v___x_770_);
lean_dec_ref(v___x_770_);
v___x_772_ = lean_string_append(v___x_768_, v___x_771_);
lean_dec_ref(v___x_771_);
v___x_773_ = l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__0(v___x_729_, v___x_720_, v___x_772_, v___x_722_);
v_a_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_774_);
v_a_775_ = lean_ctor_get(v___x_773_, 1);
lean_inc(v_a_775_);
lean_dec_ref(v___x_773_);
v___x_776_ = l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1(v_stderr_727_, v___x_712_, v___y_765_, v_a_774_, v_a_775_);
v___y_731_ = v___x_776_;
goto v___jp_730_;
}
else
{
lean_object* v___x_777_; lean_object* v___x_778_; 
lean_dec_ref(v_stdout_726_);
v___x_777_ = lean_box(0);
v___x_778_ = l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___lam__1(v_stderr_727_, v___x_712_, v___y_765_, v___x_777_, v___x_722_);
v___y_731_ = v___x_778_;
goto v___jp_730_;
}
v___jp_730_:
{
if (lean_obj_tag(v___y_731_) == 0)
{
if (v___x_729_ == 0)
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_dec_ref(v_repo_697_);
v_a_732_ = lean_ctor_get(v___y_731_, 1);
v_isSharedCheck_739_ = !lean_is_exclusive(v___y_731_);
if (v_isSharedCheck_739_ == 0)
{
lean_object* v_unused_740_; 
v_unused_740_ = lean_ctor_get(v___y_731_, 0);
lean_dec(v_unused_740_);
v___x_734_ = v___y_731_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___y_731_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 0, v___x_717_);
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v___x_717_);
lean_ctor_set(v_reuseFailAlloc_738_, 1, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
else
{
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_759_; 
v_a_741_ = lean_ctor_get(v___y_731_, 1);
v_isSharedCheck_759_ = !lean_is_exclusive(v___y_731_);
if (v_isSharedCheck_759_ == 0)
{
lean_object* v_unused_760_; 
v_unused_760_ = lean_ctor_get(v___y_731_, 0);
lean_dec(v_unused_760_);
v___x_743_ = v___y_731_;
v_isShared_744_ = v_isSharedCheck_759_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___y_731_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_759_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = ((lean_object*)(l_Lake_GitRev_fetchHead___closed__0));
lean_inc_ref(v_repo_697_);
v___x_746_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_745_, v_repo_697_);
if (lean_obj_tag(v___x_746_) == 1)
{
lean_object* v___x_748_; 
lean_dec_ref(v_repo_697_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_746_);
v___x_748_ = v___x_743_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_746_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v_a_741_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
else
{
lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_757_; 
lean_dec(v___x_746_);
v___x_750_ = ((lean_object*)(l_Lake_GitRepo_fetchRevision_x3f___closed__5));
v___x_751_ = lean_string_append(v_repo_697_, v___x_750_);
v___x_752_ = 3;
v___x_753_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_753_, 0, v___x_751_);
lean_ctor_set_uint8(v___x_753_, sizeof(void*)*1, v___x_752_);
v___x_754_ = lean_array_get_size(v_a_741_);
v___x_755_ = lean_array_push(v_a_741_, v___x_753_);
if (v_isShared_744_ == 0)
{
lean_ctor_set_tag(v___x_743_, 1);
lean_ctor_set(v___x_743_, 1, v___x_755_);
lean_ctor_set(v___x_743_, 0, v___x_754_);
v___x_757_ = v___x_743_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v___x_755_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
}
else
{
lean_object* v_a_761_; lean_object* v_a_762_; 
lean_dec_ref(v_repo_697_);
v_a_761_ = lean_ctor_get(v___y_731_, 0);
lean_inc(v_a_761_);
v_a_762_ = lean_ctor_get(v___y_731_, 1);
lean_inc(v_a_762_);
lean_dec_ref_known(v___y_731_, 2);
v_a_703_ = v_a_761_;
v_a_704_ = v_a_762_;
goto v___jp_702_;
}
}
}
else
{
lean_object* v_a_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; uint8_t v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
lean_dec_ref(v_repo_697_);
v_a_779_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_779_);
lean_dec_ref_known(v___x_723_, 1);
v___x_780_ = ((lean_object*)(l___private_Lake_Util_Git_0__Lake_GitRepo_testExecGit___closed__1));
v___x_781_ = lean_io_error_to_string(v_a_779_);
v___x_782_ = lean_string_append(v___x_780_, v___x_781_);
lean_dec_ref(v___x_781_);
v___x_783_ = 3;
v___x_784_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_784_, 0, v___x_782_);
lean_ctor_set_uint8(v___x_784_, sizeof(void*)*1, v___x_783_);
v___x_785_ = lean_array_push(v___x_722_, v___x_784_);
v_a_703_ = v___x_718_;
v_a_704_ = v___x_785_;
goto v___jp_702_;
}
v___jp_702_:
{
lean_object* v___x_705_; 
v___x_705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_705_, 0, v_a_703_);
lean_ctor_set(v___x_705_, 1, v_a_704_);
return v___x_705_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetchRevision_x3f___boxed(lean_object* v_repo_786_, lean_object* v_remote_787_, lean_object* v_rev_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lake_GitRepo_fetchRevision_x3f(v_repo_786_, v_remote_787_, v_rev_788_, v_a_789_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(lean_object* v_s_794_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0));
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___boxed(lean_object* v_s_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(v_s_796_);
lean_dec_ref(v_s_796_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(lean_object* v___x_798_, lean_object* v___x_799_, lean_object* v___x_800_, lean_object* v_a_801_, lean_object* v_b_802_){
_start:
{
lean_object* v_it_804_; lean_object* v_startInclusive_805_; lean_object* v_endExclusive_806_; 
if (lean_obj_tag(v_a_801_) == 0)
{
lean_object* v_currPos_811_; lean_object* v_searcher_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_838_; 
v_currPos_811_ = lean_ctor_get(v_a_801_, 0);
v_searcher_812_ = lean_ctor_get(v_a_801_, 1);
v_isSharedCheck_838_ = !lean_is_exclusive(v_a_801_);
if (v_isSharedCheck_838_ == 0)
{
v___x_814_ = v_a_801_;
v_isShared_815_ = v_isSharedCheck_838_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_searcher_812_);
lean_inc(v_currPos_811_);
lean_dec(v_a_801_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_838_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v_startInclusive_816_; lean_object* v_endExclusive_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v_startInclusive_816_ = lean_ctor_get(v___x_799_, 1);
v_endExclusive_817_ = lean_ctor_get(v___x_799_, 2);
v___x_818_ = lean_nat_sub(v_endExclusive_817_, v_startInclusive_816_);
v___x_819_ = lean_nat_dec_eq(v_searcher_812_, v___x_818_);
lean_dec(v___x_818_);
if (v___x_819_ == 0)
{
uint32_t v___x_820_; uint32_t v___x_821_; uint8_t v___x_822_; 
v___x_820_ = 10;
v___x_821_ = lean_string_utf8_get_fast(v___x_798_, v_searcher_812_);
v___x_822_ = lean_uint32_dec_eq(v___x_821_, v___x_820_);
if (v___x_822_ == 0)
{
lean_object* v___x_823_; lean_object* v___x_825_; 
v___x_823_ = lean_string_utf8_next_fast(v___x_798_, v_searcher_812_);
lean_dec(v_searcher_812_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 1, v___x_823_);
v___x_825_ = v___x_814_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_currPos_811_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v___x_823_);
v___x_825_ = v_reuseFailAlloc_827_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
v_a_801_ = v___x_825_;
goto _start;
}
}
else
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v_slice_831_; lean_object* v_nextIt_833_; 
v___x_828_ = lean_string_utf8_next_fast(v___x_798_, v_searcher_812_);
v___x_829_ = lean_nat_sub(v___x_828_, v_searcher_812_);
v___x_830_ = lean_nat_add(v_searcher_812_, v___x_829_);
lean_dec(v___x_829_);
v_slice_831_ = l_String_Slice_subslice_x21(v___x_799_, v_currPos_811_, v_searcher_812_);
lean_inc(v___x_830_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 1, v___x_830_);
lean_ctor_set(v___x_814_, 0, v___x_830_);
v_nextIt_833_ = v___x_814_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_830_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v___x_830_);
v_nextIt_833_ = v_reuseFailAlloc_836_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
lean_object* v_startInclusive_834_; lean_object* v_endExclusive_835_; 
v_startInclusive_834_ = lean_ctor_get(v_slice_831_, 0);
lean_inc(v_startInclusive_834_);
v_endExclusive_835_ = lean_ctor_get(v_slice_831_, 1);
lean_inc(v_endExclusive_835_);
lean_dec_ref(v_slice_831_);
v_it_804_ = v_nextIt_833_;
v_startInclusive_805_ = v_startInclusive_834_;
v_endExclusive_806_ = v_endExclusive_835_;
goto v___jp_803_;
}
}
}
else
{
lean_object* v___x_837_; 
lean_del_object(v___x_814_);
lean_dec(v_searcher_812_);
v___x_837_ = lean_box(1);
lean_inc(v___x_800_);
v_it_804_ = v___x_837_;
v_startInclusive_805_ = v_currPos_811_;
v_endExclusive_806_ = v___x_800_;
goto v___jp_803_;
}
}
}
else
{
lean_dec(v___x_800_);
lean_dec_ref(v___x_798_);
return v_b_802_;
}
v___jp_803_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
lean_inc_ref(v___x_798_);
v___x_807_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_807_, 0, v___x_798_);
lean_ctor_set(v___x_807_, 1, v_startInclusive_805_);
lean_ctor_set(v___x_807_, 2, v_endExclusive_806_);
v___x_808_ = l_String_Slice_toString(v___x_807_);
lean_dec_ref_known(v___x_807_, 3);
v___x_809_ = lean_array_push(v_b_802_, v___x_808_);
v_a_801_ = v_it_804_;
v_b_802_ = v___x_809_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg___boxed(lean_object* v___x_839_, lean_object* v___x_840_, lean_object* v___x_841_, lean_object* v_a_842_, lean_object* v_b_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v___x_839_, v___x_840_, v___x_841_, v_a_842_, v_b_843_);
lean_dec_ref(v___x_840_);
return v_res_844_;
}
}
static lean_object* _init_l_Lake_GitRepo_getHeadRevisions___closed__3(void){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_853_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevisions___closed__2));
v___x_854_ = lean_unsigned_to_nat(2u);
v___x_855_ = lean_mk_empty_array_with_capacity(v___x_854_);
v___x_856_ = lean_array_push(v___x_855_, v___x_853_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions(lean_object* v_repo_857_, lean_object* v_n_858_, lean_object* v_a_859_){
_start:
{
lean_object* v___y_862_; lean_object* v_args_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v_args_908_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevisions___closed__1));
v___x_909_ = lean_unsigned_to_nat(0u);
v___x_910_ = lean_nat_dec_eq(v_n_858_, v___x_909_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_911_ = l_Nat_reprFast(v_n_858_);
v___x_912_ = lean_obj_once(&l_Lake_GitRepo_getHeadRevisions___closed__3, &l_Lake_GitRepo_getHeadRevisions___closed__3_once, _init_l_Lake_GitRepo_getHeadRevisions___closed__3);
v___x_913_ = lean_array_push(v___x_912_, v___x_911_);
v___x_914_ = l_Array_append___redArg(v_args_908_, v___x_913_);
lean_dec_ref(v___x_913_);
v___y_862_ = v___x_914_;
goto v___jp_861_;
}
else
{
lean_dec(v_n_858_);
v___y_862_ = v_args_908_;
goto v___jp_861_;
}
v___jp_861_:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; uint8_t v___x_868_; uint8_t v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_863_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_864_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_865_, 0, v_repo_857_);
v___x_866_ = lean_unsigned_to_nat(0u);
v___x_867_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_868_ = 1;
v___x_869_ = 0;
v___x_870_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_870_, 0, v___x_863_);
lean_ctor_set(v___x_870_, 1, v___x_864_);
lean_ctor_set(v___x_870_, 2, v___y_862_);
lean_ctor_set(v___x_870_, 3, v___x_865_);
lean_ctor_set(v___x_870_, 4, v___x_867_);
lean_ctor_set_uint8(v___x_870_, sizeof(void*)*5, v___x_868_);
lean_ctor_set_uint8(v___x_870_, sizeof(void*)*5 + 1, v___x_869_);
v___x_871_ = l_Lake_captureProc_x27(v___x_870_, v_a_859_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_898_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
v_a_873_ = lean_ctor_get(v___x_871_, 1);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_898_ == 0)
{
v___x_875_ = v___x_871_;
v_isShared_876_ = v_isSharedCheck_898_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_inc(v_a_872_);
lean_dec(v___x_871_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_898_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v_stdout_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v_str_881_; lean_object* v_startInclusive_882_; lean_object* v_endExclusive_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_897_; 
v_stdout_877_ = lean_ctor_get(v_a_872_, 0);
lean_inc_ref(v_stdout_877_);
lean_dec(v_a_872_);
v___x_878_ = lean_string_utf8_byte_size(v_stdout_877_);
v___x_879_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_879_, 0, v_stdout_877_);
lean_ctor_set(v___x_879_, 1, v___x_866_);
lean_ctor_set(v___x_879_, 2, v___x_878_);
v___x_880_ = l_String_Slice_trimAscii(v___x_879_);
v_str_881_ = lean_ctor_get(v___x_880_, 0);
v_startInclusive_882_ = lean_ctor_get(v___x_880_, 1);
v_endExclusive_883_ = lean_ctor_get(v___x_880_, 2);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_897_ == 0)
{
v___x_885_ = v___x_880_;
v_isShared_886_ = v_isSharedCheck_897_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_endExclusive_883_);
lean_inc(v_startInclusive_882_);
lean_inc(v_str_881_);
lean_dec(v___x_880_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_897_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_887_ = lean_string_utf8_extract_fast(v_str_881_, v_startInclusive_882_, v_endExclusive_883_);
lean_dec(v_endExclusive_883_);
lean_dec(v_startInclusive_882_);
lean_dec_ref(v_str_881_);
v___x_888_ = lean_string_utf8_byte_size(v___x_887_);
lean_inc_ref(v___x_887_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 2, v___x_888_);
lean_ctor_set(v___x_885_, 1, v___x_866_);
lean_ctor_set(v___x_885_, 0, v___x_887_);
v___x_890_ = v___x_885_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_887_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v___x_866_);
lean_ctor_set(v_reuseFailAlloc_896_, 2, v___x_888_);
v___x_890_ = v_reuseFailAlloc_896_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_891_ = l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(v___x_890_);
v___x_892_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v___x_887_, v___x_890_, v___x_888_, v___x_891_, v___x_867_);
lean_dec_ref(v___x_890_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v___x_892_);
v___x_894_ = v___x_875_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_a_873_);
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
}
else
{
lean_object* v_a_899_; lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
v_a_899_ = lean_ctor_get(v___x_871_, 0);
v_a_900_ = lean_ctor_get(v___x_871_, 1);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_871_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_inc(v_a_899_);
lean_dec(v___x_871_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_899_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_a_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions___boxed(lean_object* v_repo_915_, lean_object* v_n_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Lake_GitRepo_getHeadRevisions(v_repo_915_, v_n_916_, v_a_917_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1(lean_object* v___x_920_, lean_object* v___x_921_, lean_object* v___x_922_, lean_object* v_inst_923_, lean_object* v_R_924_, lean_object* v_a_925_, lean_object* v_b_926_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v___x_920_, v___x_921_, v___x_922_, v_a_925_, v_b_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___boxed(lean_object* v___x_928_, lean_object* v___x_929_, lean_object* v___x_930_, lean_object* v_inst_931_, lean_object* v_R_932_, lean_object* v_a_933_, lean_object* v_b_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1(v___x_928_, v___x_929_, v___x_930_, v_inst_931_, v_R_932_, v_a_933_, v_b_934_);
lean_dec_ref(v___x_929_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object* v_rev_936_, lean_object* v_remote_937_, lean_object* v_repo_938_, lean_object* v_a_939_){
_start:
{
lean_object* v_rev_942_; lean_object* v___y_943_; uint8_t v___x_945_; 
v___x_945_ = l_Lake_GitRev_isFullSha1(v_rev_936_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_946_ = ((lean_object*)(l_Lake_GitRev_withRemote___closed__0));
v___x_947_ = lean_string_append(v_remote_937_, v___x_946_);
v___x_948_ = lean_string_append(v___x_947_, v_rev_936_);
lean_inc_ref(v_repo_938_);
v___x_949_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_948_, v_repo_938_);
if (lean_obj_tag(v___x_949_) == 1)
{
lean_object* v_val_950_; 
lean_dec_ref(v_repo_938_);
lean_dec_ref(v_rev_936_);
v_val_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_val_950_);
lean_dec_ref_known(v___x_949_, 1);
v_rev_942_ = v_val_950_;
v___y_943_ = v_a_939_;
goto v___jp_941_;
}
else
{
lean_object* v___x_951_; 
lean_dec(v___x_949_);
lean_inc_ref(v_repo_938_);
lean_inc_ref(v_rev_936_);
v___x_951_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_936_, v_repo_938_);
if (lean_obj_tag(v___x_951_) == 1)
{
lean_object* v_val_952_; 
lean_dec_ref(v_repo_938_);
lean_dec_ref(v_rev_936_);
v_val_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_val_952_);
lean_dec_ref_known(v___x_951_, 1);
v_rev_942_ = v_val_952_;
v___y_943_ = v_a_939_;
goto v___jp_941_;
}
else
{
lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; uint8_t v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
lean_dec(v___x_951_);
v___x_953_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__0));
v___x_954_ = lean_string_append(v_repo_938_, v___x_953_);
v___x_955_ = lean_string_append(v___x_954_, v_rev_936_);
lean_dec_ref(v_rev_936_);
v___x_956_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__1));
v___x_957_ = lean_string_append(v___x_955_, v___x_956_);
v___x_958_ = 3;
v___x_959_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_959_, 0, v___x_957_);
lean_ctor_set_uint8(v___x_959_, sizeof(void*)*1, v___x_958_);
v___x_960_ = lean_array_get_size(v_a_939_);
v___x_961_ = lean_array_push(v_a_939_, v___x_959_);
v___x_962_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_960_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
return v___x_962_;
}
}
}
else
{
lean_object* v___x_963_; 
lean_dec_ref(v_repo_938_);
lean_dec_ref(v_remote_937_);
v___x_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_963_, 0, v_rev_936_);
lean_ctor_set(v___x_963_, 1, v_a_939_);
return v___x_963_;
}
v___jp_941_:
{
lean_object* v___x_944_; 
v___x_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_944_, 0, v_rev_942_);
lean_ctor_set(v___x_944_, 1, v___y_943_);
return v___x_944_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___boxed(lean_object* v_rev_964_, lean_object* v_remote_965_, lean_object* v_repo_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lake_GitRepo_resolveRemoteRevision(v_rev_964_, v_remote_965_, v_repo_966_, v_a_967_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object* v_repo_970_, lean_object* v_rev_x3f_971_, lean_object* v_remote_972_, lean_object* v_a_973_){
_start:
{
lean_object* v___x_975_; 
lean_inc_ref(v_remote_972_);
lean_inc_ref(v_repo_970_);
v___x_975_ = l_Lake_GitRepo_fetch(v_repo_970_, v_remote_972_, v_a_973_);
if (lean_obj_tag(v___x_975_) == 0)
{
if (lean_obj_tag(v_rev_x3f_971_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v_a_976_ = lean_ctor_get(v___x_975_, 1);
lean_inc(v_a_976_);
lean_dec_ref_known(v___x_975_, 2);
v___x_977_ = ((lean_object*)(l_Lake_Git_upstreamBranch___closed__0));
v___x_978_ = l_Lake_GitRepo_resolveRemoteRevision(v___x_977_, v_remote_972_, v_repo_970_, v_a_976_);
return v___x_978_;
}
else
{
lean_object* v_a_979_; lean_object* v_val_980_; lean_object* v___x_981_; 
v_a_979_ = lean_ctor_get(v___x_975_, 1);
lean_inc(v_a_979_);
lean_dec_ref_known(v___x_975_, 2);
v_val_980_ = lean_ctor_get(v_rev_x3f_971_, 0);
lean_inc(v_val_980_);
lean_dec_ref_known(v_rev_x3f_971_, 1);
v___x_981_ = l_Lake_GitRepo_resolveRemoteRevision(v_val_980_, v_remote_972_, v_repo_970_, v_a_979_);
return v___x_981_;
}
}
else
{
lean_object* v_a_982_; lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
lean_dec_ref(v_remote_972_);
lean_dec(v_rev_x3f_971_);
lean_dec_ref(v_repo_970_);
v_a_982_ = lean_ctor_get(v___x_975_, 0);
v_a_983_ = lean_ctor_get(v___x_975_, 1);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_975_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_inc(v_a_982_);
lean_dec(v___x_975_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_982_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision___boxed(lean_object* v_repo_991_, lean_object* v_rev_x3f_992_, lean_object* v_remote_993_, lean_object* v_a_994_, lean_object* v_a_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lake_GitRepo_findRemoteRevision(v_repo_991_, v_rev_x3f_992_, v_remote_993_, v_a_994_);
return v_res_996_;
}
}
static lean_object* _init_l_Lake_GitRepo_branchExists___closed__2(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_999_ = ((lean_object*)(l_Lake_GitRepo_branchExists___closed__0));
v___x_1000_ = lean_unsigned_to_nat(3u);
v___x_1001_ = lean_mk_empty_array_with_capacity(v___x_1000_);
v___x_1002_ = lean_array_push(v___x_1001_, v___x_999_);
return v___x_1002_;
}
}
static lean_object* _init_l_Lake_GitRepo_branchExists___closed__3(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1003_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__0));
v___x_1004_ = lean_obj_once(&l_Lake_GitRepo_branchExists___closed__2, &l_Lake_GitRepo_branchExists___closed__2_once, _init_l_Lake_GitRepo_branchExists___closed__2);
v___x_1005_ = lean_array_push(v___x_1004_, v___x_1003_);
return v___x_1005_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_branchExists(lean_object* v_rev_1006_, lean_object* v_repo_1007_){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; uint8_t v___x_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; 
v___x_1009_ = ((lean_object*)(l_Lake_GitRepo_branchExists___closed__1));
v___x_1010_ = lean_string_append(v___x_1009_, v_rev_1006_);
v___x_1011_ = lean_obj_once(&l_Lake_GitRepo_branchExists___closed__3, &l_Lake_GitRepo_branchExists___closed__3_once, _init_l_Lake_GitRepo_branchExists___closed__3);
v___x_1012_ = lean_array_push(v___x_1011_, v___x_1010_);
v___x_1013_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_1014_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1015_, 0, v_repo_1007_);
v___x_1016_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_1017_ = 1;
v___x_1018_ = 0;
v___x_1019_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1019_, 0, v___x_1013_);
lean_ctor_set(v___x_1019_, 1, v___x_1014_);
lean_ctor_set(v___x_1019_, 2, v___x_1012_);
lean_ctor_set(v___x_1019_, 3, v___x_1015_);
lean_ctor_set(v___x_1019_, 4, v___x_1016_);
lean_ctor_set_uint8(v___x_1019_, sizeof(void*)*5, v___x_1017_);
lean_ctor_set_uint8(v___x_1019_, sizeof(void*)*5 + 1, v___x_1018_);
v___x_1020_ = l_Lake_testProc(v___x_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_branchExists___boxed(lean_object* v_rev_1021_, lean_object* v_repo_1022_, lean_object* v_a_1023_){
_start:
{
uint8_t v_res_1024_; lean_object* v_r_1025_; 
v_res_1024_ = l_Lake_GitRepo_branchExists(v_rev_1021_, v_repo_1022_);
lean_dec_ref(v_rev_1021_);
v_r_1025_ = lean_box(v_res_1024_);
return v_r_1025_;
}
}
static lean_object* _init_l_Lake_GitRepo_revisionExists___closed__0(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1026_ = ((lean_object*)(l_Lake_GitRepo_insideWorkTree___closed__0));
v___x_1027_ = lean_unsigned_to_nat(3u);
v___x_1028_ = lean_mk_empty_array_with_capacity(v___x_1027_);
v___x_1029_ = lean_array_push(v___x_1028_, v___x_1026_);
return v___x_1029_;
}
}
static lean_object* _init_l_Lake_GitRepo_revisionExists___closed__1(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1030_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__0));
v___x_1031_ = lean_obj_once(&l_Lake_GitRepo_revisionExists___closed__0, &l_Lake_GitRepo_revisionExists___closed__0_once, _init_l_Lake_GitRepo_revisionExists___closed__0);
v___x_1032_ = lean_array_push(v___x_1031_, v___x_1030_);
return v___x_1032_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_revisionExists(lean_object* v_rev_1033_, lean_object* v_repo_1034_){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; uint8_t v___x_1045_; lean_object* v___x_1046_; uint8_t v___x_1047_; 
v___x_1036_ = ((lean_object*)(l_Lake_GitRepo_findCommit_x3f___closed__0));
v___x_1037_ = lean_string_append(v_rev_1033_, v___x_1036_);
v___x_1038_ = lean_obj_once(&l_Lake_GitRepo_revisionExists___closed__1, &l_Lake_GitRepo_revisionExists___closed__1_once, _init_l_Lake_GitRepo_revisionExists___closed__1);
v___x_1039_ = lean_array_push(v___x_1038_, v___x_1037_);
v___x_1040_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_1041_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1042_, 0, v_repo_1034_);
v___x_1043_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_1044_ = 1;
v___x_1045_ = 0;
v___x_1046_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1046_, 0, v___x_1040_);
lean_ctor_set(v___x_1046_, 1, v___x_1041_);
lean_ctor_set(v___x_1046_, 2, v___x_1039_);
lean_ctor_set(v___x_1046_, 3, v___x_1042_);
lean_ctor_set(v___x_1046_, 4, v___x_1043_);
lean_ctor_set_uint8(v___x_1046_, sizeof(void*)*5, v___x_1044_);
lean_ctor_set_uint8(v___x_1046_, sizeof(void*)*5 + 1, v___x_1045_);
v___x_1047_ = l_Lake_testProc(v___x_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_revisionExists___boxed(lean_object* v_rev_1048_, lean_object* v_repo_1049_, lean_object* v_a_1050_){
_start:
{
uint8_t v_res_1051_; lean_object* v_r_1052_; 
v_res_1051_ = l_Lake_GitRepo_revisionExists(v_rev_1048_, v_repo_1049_);
v_r_1052_ = lean_box(v_res_1051_);
return v_r_1052_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags(lean_object* v_repo_1058_){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; uint8_t v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1060_ = ((lean_object*)(l_Lake_GitRepo_getTags___closed__1));
v___x_1061_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_1062_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1063_, 0, v_repo_1058_);
v___x_1064_ = lean_unsigned_to_nat(0u);
v___x_1065_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_1066_ = 1;
v___x_1067_ = 0;
v___x_1068_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1068_, 0, v___x_1061_);
lean_ctor_set(v___x_1068_, 1, v___x_1062_);
lean_ctor_set(v___x_1068_, 2, v___x_1060_);
lean_ctor_set(v___x_1068_, 3, v___x_1063_);
lean_ctor_set(v___x_1068_, 4, v___x_1065_);
lean_ctor_set_uint8(v___x_1068_, sizeof(void*)*5, v___x_1066_);
lean_ctor_set_uint8(v___x_1068_, sizeof(void*)*5 + 1, v___x_1067_);
v___x_1069_ = l_Lake_captureProc_x3f(v___x_1068_);
if (lean_obj_tag(v___x_1069_) == 1)
{
lean_object* v_val_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_val_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc_n(v_val_1070_, 2);
lean_dec_ref_known(v___x_1069_, 1);
v___x_1071_ = lean_string_utf8_byte_size(v_val_1070_);
v___x_1072_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1072_, 0, v_val_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1064_);
lean_ctor_set(v___x_1072_, 2, v___x_1071_);
v___x_1073_ = l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(v___x_1072_);
v___x_1074_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v_val_1070_, v___x_1072_, v___x_1071_, v___x_1073_, v___x_1065_);
lean_dec_ref_known(v___x_1072_, 3);
v___x_1075_ = lean_array_to_list(v___x_1074_);
return v___x_1075_;
}
else
{
lean_object* v___x_1076_; 
lean_dec(v___x_1069_);
v___x_1076_ = lean_box(0);
return v___x_1076_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags___boxed(lean_object* v_repo_1077_, lean_object* v_a_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lake_GitRepo_getTags(v_repo_1077_);
return v_res_1079_;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__2(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1082_ = ((lean_object*)(l_Lake_GitRepo_findTag_x3f___closed__0));
v___x_1083_ = lean_unsigned_to_nat(4u);
v___x_1084_ = lean_mk_empty_array_with_capacity(v___x_1083_);
v___x_1085_ = lean_array_push(v___x_1084_, v___x_1082_);
return v___x_1085_;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__3(void){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1086_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__1));
v___x_1087_ = lean_obj_once(&l_Lake_GitRepo_findTag_x3f___closed__2, &l_Lake_GitRepo_findTag_x3f___closed__2_once, _init_l_Lake_GitRepo_findTag_x3f___closed__2);
v___x_1088_ = lean_array_push(v___x_1087_, v___x_1086_);
return v___x_1088_;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__4(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1089_ = ((lean_object*)(l_Lake_GitRepo_findTag_x3f___closed__1));
v___x_1090_ = lean_obj_once(&l_Lake_GitRepo_findTag_x3f___closed__3, &l_Lake_GitRepo_findTag_x3f___closed__3_once, _init_l_Lake_GitRepo_findTag_x3f___closed__3);
v___x_1091_ = lean_array_push(v___x_1090_, v___x_1089_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f(lean_object* v_rev_1092_, lean_object* v_repo_1093_){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; uint8_t v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1095_ = lean_obj_once(&l_Lake_GitRepo_findTag_x3f___closed__4, &l_Lake_GitRepo_findTag_x3f___closed__4_once, _init_l_Lake_GitRepo_findTag_x3f___closed__4);
v___x_1096_ = lean_array_push(v___x_1095_, v_rev_1092_);
v___x_1097_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_1098_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1099_, 0, v_repo_1093_);
v___x_1100_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_1101_ = 1;
v___x_1102_ = 0;
v___x_1103_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1103_, 0, v___x_1097_);
lean_ctor_set(v___x_1103_, 1, v___x_1098_);
lean_ctor_set(v___x_1103_, 2, v___x_1096_);
lean_ctor_set(v___x_1103_, 3, v___x_1099_);
lean_ctor_set(v___x_1103_, 4, v___x_1100_);
lean_ctor_set_uint8(v___x_1103_, sizeof(void*)*5, v___x_1101_);
lean_ctor_set_uint8(v___x_1103_, sizeof(void*)*5 + 1, v___x_1102_);
v___x_1104_ = l_Lake_captureProc_x3f(v___x_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f___boxed(lean_object* v_rev_1105_, lean_object* v_repo_1106_, lean_object* v_a_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lake_GitRepo_findTag_x3f(v_rev_1105_, v_repo_1106_);
return v_res_1108_;
}
}
static lean_object* _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__2(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1111_ = ((lean_object*)(l_Lake_GitRepo_getRemoteUrl_x3f___closed__0));
v___x_1112_ = lean_unsigned_to_nat(3u);
v___x_1113_ = lean_mk_empty_array_with_capacity(v___x_1112_);
v___x_1114_ = lean_array_push(v___x_1113_, v___x_1111_);
return v___x_1114_;
}
}
static lean_object* _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__3(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1115_ = ((lean_object*)(l_Lake_GitRepo_getRemoteUrl_x3f___closed__1));
v___x_1116_ = lean_obj_once(&l_Lake_GitRepo_getRemoteUrl_x3f___closed__2, &l_Lake_GitRepo_getRemoteUrl_x3f___closed__2_once, _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__2);
v___x_1117_ = lean_array_push(v___x_1116_, v___x_1115_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object* v_remote_1118_, lean_object* v_repo_1119_){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; uint8_t v___x_1127_; uint8_t v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1121_ = lean_obj_once(&l_Lake_GitRepo_getRemoteUrl_x3f___closed__3, &l_Lake_GitRepo_getRemoteUrl_x3f___closed__3_once, _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__3);
v___x_1122_ = lean_array_push(v___x_1121_, v_remote_1118_);
v___x_1123_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_1124_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1125_, 0, v_repo_1119_);
v___x_1126_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_1127_ = 1;
v___x_1128_ = 0;
v___x_1129_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1129_, 0, v___x_1123_);
lean_ctor_set(v___x_1129_, 1, v___x_1124_);
lean_ctor_set(v___x_1129_, 2, v___x_1122_);
lean_ctor_set(v___x_1129_, 3, v___x_1125_);
lean_ctor_set(v___x_1129_, 4, v___x_1126_);
lean_ctor_set_uint8(v___x_1129_, sizeof(void*)*5, v___x_1127_);
lean_ctor_set_uint8(v___x_1129_, sizeof(void*)*5 + 1, v___x_1128_);
v___x_1130_ = l_Lake_captureProc_x3f(v___x_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___boxed(lean_object* v_remote_1131_, lean_object* v_repo_1132_, lean_object* v_a_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Lake_GitRepo_getRemoteUrl_x3f(v_remote_1131_, v_repo_1132_);
return v_res_1134_;
}
}
static lean_object* _init_l_Lake_GitRepo_addRemote___closed__0(void){
_start:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1135_ = ((lean_object*)(l_Lake_GitRepo_getRemoteUrl_x3f___closed__0));
v___x_1136_ = lean_unsigned_to_nat(4u);
v___x_1137_ = lean_mk_empty_array_with_capacity(v___x_1136_);
v___x_1138_ = lean_array_push(v___x_1137_, v___x_1135_);
return v___x_1138_;
}
}
static lean_object* _init_l_Lake_GitRepo_addRemote___closed__1(void){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1139_ = ((lean_object*)(l_Lake_GitRepo_addWorktreeDetach___closed__1));
v___x_1140_ = lean_obj_once(&l_Lake_GitRepo_addRemote___closed__0, &l_Lake_GitRepo_addRemote___closed__0_once, _init_l_Lake_GitRepo_addRemote___closed__0);
v___x_1141_ = lean_array_push(v___x_1140_, v___x_1139_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_addRemote(lean_object* v_remote_1142_, lean_object* v_url_1143_, lean_object* v_repo_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; uint8_t v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1147_ = lean_obj_once(&l_Lake_GitRepo_addRemote___closed__1, &l_Lake_GitRepo_addRemote___closed__1_once, _init_l_Lake_GitRepo_addRemote___closed__1);
v___x_1148_ = lean_array_push(v___x_1147_, v_remote_1142_);
v___x_1149_ = lean_array_push(v___x_1148_, v_url_1143_);
v___x_1150_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_1151_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1152_, 0, v_repo_1144_);
v___x_1153_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_1154_ = 1;
v___x_1155_ = 0;
v___x_1156_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1156_, 0, v___x_1150_);
lean_ctor_set(v___x_1156_, 1, v___x_1151_);
lean_ctor_set(v___x_1156_, 2, v___x_1149_);
lean_ctor_set(v___x_1156_, 3, v___x_1152_);
lean_ctor_set(v___x_1156_, 4, v___x_1153_);
lean_ctor_set_uint8(v___x_1156_, sizeof(void*)*5, v___x_1154_);
lean_ctor_set_uint8(v___x_1156_, sizeof(void*)*5 + 1, v___x_1155_);
v___x_1157_ = lean_box(0);
v___x_1158_ = l_Lake_proc(v___x_1156_, v___x_1154_, v___x_1157_, v_a_1145_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_addRemote___boxed(lean_object* v_remote_1159_, lean_object* v_url_1160_, lean_object* v_repo_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lake_GitRepo_addRemote(v_remote_1159_, v_url_1160_, v_repo_1161_, v_a_1162_);
return v_res_1164_;
}
}
static lean_object* _init_l_Lake_GitRepo_setRemoteUrl___closed__1(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1166_ = ((lean_object*)(l_Lake_GitRepo_setRemoteUrl___closed__0));
v___x_1167_ = lean_obj_once(&l_Lake_GitRepo_addRemote___closed__0, &l_Lake_GitRepo_addRemote___closed__0_once, _init_l_Lake_GitRepo_addRemote___closed__0);
v___x_1168_ = lean_array_push(v___x_1167_, v___x_1166_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_setRemoteUrl(lean_object* v_remote_1169_, lean_object* v_url_1170_, lean_object* v_repo_1171_, lean_object* v_a_1172_){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; uint8_t v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1174_ = lean_obj_once(&l_Lake_GitRepo_setRemoteUrl___closed__1, &l_Lake_GitRepo_setRemoteUrl___closed__1_once, _init_l_Lake_GitRepo_setRemoteUrl___closed__1);
v___x_1175_ = lean_array_push(v___x_1174_, v_remote_1169_);
v___x_1176_ = lean_array_push(v___x_1175_, v_url_1170_);
v___x_1177_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_1178_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1179_, 0, v_repo_1171_);
v___x_1180_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_1181_ = 1;
v___x_1182_ = 0;
v___x_1183_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1183_, 0, v___x_1177_);
lean_ctor_set(v___x_1183_, 1, v___x_1178_);
lean_ctor_set(v___x_1183_, 2, v___x_1176_);
lean_ctor_set(v___x_1183_, 3, v___x_1179_);
lean_ctor_set(v___x_1183_, 4, v___x_1180_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*5, v___x_1181_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*5 + 1, v___x_1182_);
v___x_1184_ = lean_box(0);
v___x_1185_ = l_Lake_proc(v___x_1183_, v___x_1181_, v___x_1184_, v_a_1172_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_setRemoteUrl___boxed(lean_object* v_remote_1186_, lean_object* v_url_1187_, lean_object* v_repo_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lake_GitRepo_setRemoteUrl(v_remote_1186_, v_url_1187_, v_repo_1188_, v_a_1189_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object* v_remote_1192_, lean_object* v_repo_1193_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Lake_GitRepo_getRemoteUrl_x3f(v_remote_1192_, v_repo_1193_);
if (lean_obj_tag(v___x_1195_) == 0)
{
return v___x_1195_;
}
else
{
lean_object* v_val_1196_; lean_object* v___x_1197_; 
v_val_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc(v_val_1196_);
lean_dec_ref_known(v___x_1195_, 1);
v___x_1197_ = l_Lake_Git_filterUrl_x3f(v_val_1196_);
return v___x_1197_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f___boxed(lean_object* v_remote_1198_, lean_object* v_repo_1199_, lean_object* v_a_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(v_remote_1198_, v_repo_1199_);
return v_res_1201_;
}
}
static lean_object* _init_l_Lake_GitRepo_pruneRemote___closed__1(void){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1203_ = ((lean_object*)(l_Lake_GitRepo_pruneRemote___closed__0));
v___x_1204_ = lean_obj_once(&l_Lake_GitRepo_getRemoteUrl_x3f___closed__2, &l_Lake_GitRepo_getRemoteUrl_x3f___closed__2_once, _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__2);
v___x_1205_ = lean_array_push(v___x_1204_, v___x_1203_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_pruneRemote(lean_object* v_remote_1206_, lean_object* v_repo_1207_, lean_object* v_a_1208_){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; uint8_t v___x_1216_; uint8_t v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1210_ = lean_obj_once(&l_Lake_GitRepo_pruneRemote___closed__1, &l_Lake_GitRepo_pruneRemote___closed__1_once, _init_l_Lake_GitRepo_pruneRemote___closed__1);
v___x_1211_ = lean_array_push(v___x_1210_, v_remote_1206_);
v___x_1212_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_1213_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1214_, 0, v_repo_1207_);
v___x_1215_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_1216_ = 1;
v___x_1217_ = 0;
v___x_1218_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1218_, 0, v___x_1212_);
lean_ctor_set(v___x_1218_, 1, v___x_1213_);
lean_ctor_set(v___x_1218_, 2, v___x_1211_);
lean_ctor_set(v___x_1218_, 3, v___x_1214_);
lean_ctor_set(v___x_1218_, 4, v___x_1215_);
lean_ctor_set_uint8(v___x_1218_, sizeof(void*)*5, v___x_1216_);
lean_ctor_set_uint8(v___x_1218_, sizeof(void*)*5 + 1, v___x_1217_);
v___x_1219_ = lean_box(0);
v___x_1220_ = l_Lake_proc(v___x_1218_, v___x_1216_, v___x_1219_, v_a_1208_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_pruneRemote___boxed(lean_object* v_remote_1221_, lean_object* v_repo_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lake_GitRepo_pruneRemote(v_remote_1221_, v_repo_1222_, v_a_1223_);
return v_res_1225_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasNoDiff(lean_object* v_repo_1236_){
_start:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; uint8_t v___x_1243_; uint8_t v___x_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1238_ = ((lean_object*)(l_Lake_GitRepo_hasNoDiff___closed__2));
v___x_1239_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_1240_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1241_, 0, v_repo_1236_);
v___x_1242_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_1243_ = 1;
v___x_1244_ = 0;
v___x_1245_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1245_, 0, v___x_1239_);
lean_ctor_set(v___x_1245_, 1, v___x_1240_);
lean_ctor_set(v___x_1245_, 2, v___x_1238_);
lean_ctor_set(v___x_1245_, 3, v___x_1241_);
lean_ctor_set(v___x_1245_, 4, v___x_1242_);
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*5, v___x_1243_);
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*5 + 1, v___x_1244_);
v___x_1246_ = l_Lake_testProc(v___x_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasNoDiff___boxed(lean_object* v_repo_1247_, lean_object* v_a_1248_){
_start:
{
uint8_t v_res_1249_; lean_object* v_r_1250_; 
v_res_1249_ = l_Lake_GitRepo_hasNoDiff(v_repo_1247_);
v_r_1250_ = lean_box(v_res_1249_);
return v_r_1250_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasDiff(lean_object* v_repo_1251_){
_start:
{
uint8_t v___x_1253_; 
v___x_1253_ = l_Lake_GitRepo_hasNoDiff(v_repo_1251_);
if (v___x_1253_ == 0)
{
uint8_t v___x_1254_; 
v___x_1254_ = 1;
return v___x_1254_;
}
else
{
uint8_t v___x_1255_; 
v___x_1255_ = 0;
return v___x_1255_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasDiff___boxed(lean_object* v_repo_1256_, lean_object* v_a_1257_){
_start:
{
uint8_t v_res_1258_; lean_object* v_r_1259_; 
v_res_1258_ = l_Lake_GitRepo_hasDiff(v_repo_1256_);
v_r_1259_ = lean_box(v_res_1258_);
return v_r_1259_;
}
}
lean_object* runtime_initialize_Init_Data_ToString(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Proc(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_String(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Git(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Proc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_Git(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString(uint8_t builtin);
lean_object* initialize_Lake_Util_Proc(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Lake_Util_String(uint8_t builtin);
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
res = initialize_Lake_Util_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Git(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_Git(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_Git(builtin);
}
#ifdef __cplusplus
}
#endif
