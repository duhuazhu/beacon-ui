#!/bin/sh
# 堵死中兴 OTA（固件在线升级）。三层，都可以重复执行（开机由 rc.local 跑一次，idle-guard 每 5 分钟补一次）：
#   1. /etc/hosts：zte_dm 内置的升级服务器 https://dm{s,can,eu,cn}[6].ztems.com 全部指向本机（IPv4 + IPv6，
#      只写 IPv4 的话，只查 IPv6 的程序会绕过 hosts 去问 DNS）。原来只挡了 dmcn / ztems.com，dms / dms6 是通的。
#   2. 防火墙兜底：本机发出的 80/443 连接里出现 "ztems.com"（TLS 握手的 SNI、HTTP 的 Host）一律拒绝——
#      写死 IP、自己查 DNS 的也连不上。只管本机发出（OUTPUT），不碰转发给客户端的流量。
#   3. TR-069：原厂防火墙对蜂窝侧放行 7547（运营商远程管理），这里在它前面丢掉。
#   另外并入 UFI-TOOLS 的「ZTE 系统更新 / 遥测 屏蔽」清单（遥测、智能家居等域名进 hosts，两个 IP 进防火墙）。
# 不改原厂程序、不改原厂配置（/etc/config/*），不停原厂服务（停 zte_dm 等会卡开机 logo）。
#   ota-block.sh            套用 / 补回
#   ota-block.sh status     看三层是否都在
#   ota-block.sh off        全部撤掉（hosts 里只删自己加的那段）
H=/etc/hosts
MARK="# ota-block"
# OTA 服务器（zte_dm 内置）
NAMES="ztems.com www.ztems.com dms.ztems.com dms6.ztems.com dmcan.ztems.com dmcan6.ztems.com dmeu.ztems.com dmeu6.ztems.com dmcn.ztems.com dmcn6.ztems.com"
# UFI-TOOLS「ZTE 系统更新 / 遥测 屏蔽」清单里的其余域名：并进来，UFI 那段被移除 / 覆盖也照样挡
NAMES="$NAMES ctm.zte.com.cn zx.zte.com.cn report.server.nubia.cn www.myzte.cn myzte.cn ztedevice.com ztesmarthome.com rot-dispatch-asia.ztesmarthome.com seecom.com.cn ufi.seecom.com.cn"
# 固件里实际内置、两份清单都没有的：zte_oss_client 日志上报、dadian 埋点（release / debug）、智家云连接
NAMES="$NAMES fb.ztems.com api-data.nubia.com api-data-test.nubia.com zmesh-link.ztehome.com.cn"
# UFI-TOOLS 安卓版（F50）清单里的服务子域名
NAMES="$NAMES link.ztehome.com.cn asia.ztesmarthome.com rot-dispatch-eu.ztesmarthome.com rot-dispatch-link.ztehome.com.cn rot-dispatch-fmc.zx.zte.com.cn rot-dispatch-fmc-test2.zx.zte.com.cn"
# 故意不挡：ufi.ztedevice.com 是本机管理页的局域网域名（zwrt_router.dnsmasq.localdomain）；
# zte.com.cn / nubia.cn / ztedevices.com / ztehome.com.cn 这些官网主域名固件不连，挡了也没用。
# 注意：这些 hosts 只管 U60 本机的程序（zte_dm 等走系统解析）；局域网设备的 DNS 若经过不读 /etc/hosts 的转发，
# 对手机电脑就不生效（2026-10-11 实测 myzte.cn 从 Mac 照样连得到真服务器）
# 同一清单里写成 IP 的两项：hosts 挡不了 IP，由防火墙直接拒绝
IPS="61.145.136.87 36.133.8.210"
CH=OTA_BLOCK

hosts_on() {
    want=$(for n in $NAMES; do printf '127.0.0.1 %s %s\n::1 %s %s\n' "$n" "$MARK" "$n" "$MARK"; done)
    [ "$(grep -F "$MARK" $H 2>/dev/null)" = "$want" ] && return 0
    { grep -v -F "$MARK" $H; echo "$want"; } > $H.ota && cat $H.ota > $H && rm -f $H.ota   # same inode
}
hosts_off() { grep -q -F "$MARK" $H && { grep -v -F "$MARK" $H > $H.ota && cat $H.ota > $H; rm -f $H.ota; }; return 0; }

fw_on() {
    for t in iptables ip6tables; do
        $t -w 5 -N $CH 2>/dev/null
        ok=1
        $t -w 5 -C $CH -p tcp -m multiport --dports 80,443 -m string --algo bm --string ztems.com -j REJECT --reject-with tcp-reset 2>/dev/null || ok=0
        [ $t = iptables ] && for ip in $IPS; do $t -w 5 -C $CH -d $ip -j REJECT 2>/dev/null || ok=0; done
        if [ $ok = 0 ]; then                  # rebuild the whole chain: never a half set
            $t -w 5 -F $CH
            $t -w 5 -A $CH -p tcp -m multiport --dports 80,443 -m string --algo bm --string ztems.com -j REJECT --reject-with tcp-reset
            [ $t = iptables ] && for ip in $IPS; do $t -w 5 -A $CH -d $ip -j REJECT; done
        fi
        $t -w 5 -C OUTPUT -j $CH 2>/dev/null || $t -w 5 -I OUTPUT 1 -j $CH
        $t -w 5 -C INPUT -i rmnet+ -p tcp --dport 7547 -j DROP 2>/dev/null || $t -w 5 -I INPUT 1 -i rmnet+ -p tcp --dport 7547 -j DROP
    done
}
fw_off() {
    for t in iptables ip6tables; do
        while $t -w 5 -D OUTPUT -j $CH 2>/dev/null; do :; done
        $t -w 5 -F $CH 2>/dev/null; $t -w 5 -X $CH 2>/dev/null
        while $t -w 5 -D INPUT -i rmnet+ -p tcp --dport 7547 -j DROP 2>/dev/null; do :; done
    done
}

case "$1" in
    status)
        n=$(grep -c -F "$MARK" $H); echo "hosts: $n 行（应为 $(( $(echo $NAMES | wc -w) * 2 ))）"
        for t in iptables ip6tables; do
            echo "$t: OUTPUT->$CH $($t -C OUTPUT -j $CH 2>/dev/null && echo 在 || echo 缺)，7547 $($t -C INPUT -i rmnet+ -p tcp --dport 7547 -j DROP 2>/dev/null && echo 在 || echo 缺)，链内 $($t -S $CH 2>/dev/null | grep -c '^-A') 条"
        done ;;
    off) hosts_off; fw_off ;;
    *) hosts_on; fw_on ;;
esac
exit 0
