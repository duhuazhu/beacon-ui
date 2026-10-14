#ifndef UPDATE_H
#define UPDATE_H

/* 开源版不含在线更新，下面的路径只给屏幕的升级状态读取代码用 */
#define UPD_DIR    "/data/plugins/u60pro-devui"
#define UPD_CLI    UPD_DIR "/devupd"
#define UPD_STATE  "/tmp/u60-upg.state"
#define UPD_FILE   "/data/plugins/.u60-stage/bundle.tar.gz"

int update_maybe_check(void);
int update_cli(int argc, char **argv);

#endif
