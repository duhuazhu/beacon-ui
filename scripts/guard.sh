#!/bin/sh
# Boot hand-over + watchdog for the custom screen UI.
# start.sh stops the vendor UI (which stays *enabled* for early panel bring-up)
# and starts ours. If ours dies it is restarted; after 3 deaths the panel is
# handed back to the vendor UI so the screen is never left dark.
# Pause (e.g. while swapping the binary): touch /tmp/u60pro-devui-pause
D=/data/plugins/u60pro-devui
# single instance: rc.local may be re-run; a second watchdog could start a second UI
PIDF=/tmp/u60pro-guard.pid
old=$(cat $PIDF 2>/dev/null)
if [ -n "$old" ] && [ "$old" != $$ ] && kill -0 "$old" 2>/dev/null && grep -q "u60pro-devui/guard.sh" /proc/$old/cmdline 2>/dev/null; then
    exit 0
fi
echo $$ > $PIDF
L=/tmp/u60pro-guard.log
glog() {   # 日志在内存盘上，超过 64K 只留后半
    echo "$(date '+%F %T') $*" >> $L
    [ "$(wc -c < $L)" -gt 65536 ] && tail -c 32768 $L > $L.n && mv $L.n $L
    return 0
}
# 屏幕进程：comm 是 u60pro-devui 的进程（relayd/devupd 软链的 comm 是软链名，不会认错；busybox pidof 会认错）。
# 先看 pid 文件，失效再扫 /proc：老版本不写 pid 文件。read 是内建命令，扫一遍不额外起进程
ui_pids() {
    p=$(cat /tmp/u60pro-devui.pid 2>/dev/null)
    if [ -n "$p" ] && read -r c 2>/dev/null < /proc/$p/comm && [ "$c" = u60pro-devui ]; then echo "$p"; return 0; fi
    for d in /proc/[0-9]*; do read -r c 2>/dev/null < $d/comm && [ "$c" = u60pro-devui ] && echo "${d#/proc/}"; done
    return 0
}
ui_alive() { [ -n "$(ui_pids)" ]; }
ui_alive || sh $D/start.sh legacy   # don't start a second UI if one is up
fails=0
up=0                    # seconds the current instance has been seen alive
n=0
while true; do
    sleep 10
    n=$((n + 1))
    [ -f /tmp/u60pro-devui-pause ] && continue
    # 后端数据服务挂了屏幕就一直没数据：每 30 秒看一眼，没了就拉起；拉不起只记一次日志
    # （充电开机不跑 datad，start.sh 返回 3 之后就不再试）
    if [ $((n % 3)) = 0 ] && [ -z "$dskip" ] && [ -f $D/start.sh ]; then
        if pidof zwrt-datad >/dev/null; then
            dwarn=0
        else
            sh $D/start.sh datad; rc=$?
            if [ $rc = 3 ]; then
                dskip=1
            elif pidof zwrt-datad >/dev/null; then
                glog "datad gone, restarted pid $(pidof zwrt-datad)"
            elif [ "${dwarn:-0}" = 0 ]; then
                glog "datad gone and failed to start"; dwarn=1
            fi
        fi
    fi
    if ui_alive; then
        up=$((up + 10))
        [ $up -ge 600 ] && fails=0      # stable for 10 min: forget earlier crashes
        continue
    fi
    up=0
    fails=$((fails + 1))
    glog "devui gone, restart #$fails"
    if [ $fails -ge 3 ]; then
        glog "giving the panel back to zte_topsw_devui"
        /etc/init.d/zte_topsw_devui start
        exit 0
    fi
    nohup $D/u60pro-devui >>/tmp/u60pro-devui.log 2>&1 </dev/null &   # 追加模式：idle-guard 截短日志时偏移才会跟着变
done
