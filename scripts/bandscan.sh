#!/bin/sh
# 扫描所有频段（附近基站页）：把 5G SA 依次临时锁到国内在用的频段，每个频段等它连上、
# 记下服务小区的信号，最后把原来的锁频原样写回。
#   状态 /tmp/u60-bandscan.state   "run n78 <第几个> <共几个> <时间>" | "done <时间>" | "stopped <时间>" | "fail <时间> <原因>"
#   结果 /tmp/u60-bandscan.res     每行 "n78 ok <rsrp> <sinr> <pci> <arfcn>" 或 "n41 none"
#   当前 /tmp/u60-bandscan.cur     扫描前正在用的频段（结果里标「当前」）
#   原值 /tmp/u60-bandscan.orig    扫描前的 nr5g_sa_band_lock；扫完 / 停止 / 被杀都会写回，
#                                  脚本没了文件还在时由 idle-guard.sh 兜底写回
#   停止 touch /tmp/u60-bandscan.stop
S=/tmp/u60-bandscan.state; R=/tmp/u60-bandscan.res; C=/tmp/u60-bandscan.cur
O=/tmp/u60-bandscan.orig; STOP=/tmp/u60-bandscan.stop; P=/tmp/u60-bandscan.pid
BANDS="78 41 28 1 3 5 8 79"          # 国内运营商在用的 5G 频段（本机支持的才扫）
WAIT_MAX=10                          # 每个频段最多等几秒
NI='ubus -t 5 call zte_nwinfo_api'

exec 9>/tmp/u60-bandscan.lock
flock -n 9 || exit 0                  # 已经有一次在扫
rm -f $STOP
: > $R

# "key": value / "key": "value" -> value
field() { echo "$1" | sed -n "s/^[[:space:]]*\"$2\":[[:space:]]*\"\{0,1\}\([^\",]*\)\"\{0,1\},\{0,1\}[[:space:]]*$/\1/p" | head -1; }
# quoted string that may contain commas ("1,2,3,…")
fstr() { echo "$1" | sed -n "s/^[[:space:]]*\"$2\":[[:space:]]*\"\([^\"]*\)\".*/\1/p" | head -1; }

J=$($NI nwinfo_get_netinfo 2>/dev/null)
orig=$(fstr "$J" nr5g_sa_band_lock)
if [ -z "$orig" ]; then echo "fail $(date +%s) noinfo" > $S; exit 1; fi
echo "$orig" > $O
echo $$ > $P
field "$J" nr5g_action_band > $C

restore() {
    o=$(cat $O 2>/dev/null)
    [ -n "$o" ] && $NI nwinfo_set_nrbandlock "{\"nr5g_type\":\"0\",\"nr5g_band\":\"$o\"}" >/dev/null 2>&1
    rm -f $O $P
}
trap 'restore; echo "stopped $(date +%s)" > $S; rm -f $STOP; exit 0' INT TERM HUP

total=0
for b in $BANDS; do case ",$orig," in *",$b,"*) total=$((total + 1)) ;; esac; done
n=0
for b in $BANDS; do
    case ",$orig," in *",$b,"*) ;; *) continue ;; esac
    [ -f $STOP ] && break
    n=$((n + 1))
    echo "run n$b $n $total $(date +%s)" > $S
    $NI nwinfo_set_nrbandlock "{\"nr5g_type\":\"0\",\"nr5g_band\":\"$b\"}" >/dev/null 2>&1
    best=""; br=-999; att=0; i=0
    while [ $i -lt $WAIT_MAX ]; do
        sleep 1; i=$((i + 1))
        [ -f $STOP ] && break
        J=$($NI nwinfo_get_netinfo 2>/dev/null)
        [ "$(field "$J" network_type)" = SA ] || continue
        [ "$(field "$J" nr5g_action_band)" = "n$b" ] || continue
        r=$(field "$J" nr5g_rsrp)
        [ "$r" -lt 0 ] 2>/dev/null || continue
        [ $att -eq 0 ] && att=$i
        if [ "$r" -gt "$br" ]; then
            br=$r
            best="$r $(field "$J" nr5g_snr) $(field "$J" nr5g_pci) $(field "$J" nr5g_action_channel)"
        fi
        [ $i -ge $((att + 2)) ] && break      # 连上后再看两秒，取最好的一次
    done
    if [ -n "$best" ]; then echo "n$b ok $best" >> $R; else echo "n$b none" >> $R; fi
done

restore
if [ -f $STOP ]; then echo "stopped $(date +%s)" > $S; else echo "done $(date +%s)" > $S; fi
rm -f $STOP
