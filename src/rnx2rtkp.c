/*------------------------------------------------------------------------------
* rnx2rtkp.c : read rinex obs/nav files and compute receiver positions
*
*          Copyright (C) 2007-2016 by T.TAKASU, All rights reserved.
*
* version : $Revision: 1.1 $ $Date: 2008/07/17 21:55:16 $
* history : 2007/01/16  1.0 new
*           2007/03/15  1.1 add library mode
*           2007/05/08  1.2 separate from postpos.c
*           2009/01/20  1.3 support rtklib 2.2.0 api
*           2009/12/12  1.4 support glonass
*                           add option -h, -a, -l, -x
*           2010/01/28  1.5 add option -k
*           2010/08/12  1.6 add option -y implementation (2.4.0_p1)
*           2014/01/27  1.7 fix bug on default output time format
*           2015/05/15  1.8 -r or -l options for fixed or ppp-fixed mode
*           2015/06/12  1.9 output patch level in header
*           2016/09/07  1.10 add option -sys
*-----------------------------------------------------------------------------*/
#include <stdarg.h>
#include "rtklib.h"

#define PROGNAME    "rnx2rtkp"          /* program name */
#define MAXFILE     16                  /* max number of input files */

/* help text -----------------------------------------------------------------*/
static const char *help[]={
"",
" usage: rnx2rtkp [option]... file file [...]",
"",
" Read RINEX OBS/NAV/GNAV/HNAV/CLK, SP3, SBAS message log files and ccompute ",
" receiver (rover) positions and output position solutions.",
" The first RINEX OBS file shall contain receiver (rover) observations. For the",
" relative mode, the second RINEX OBS file shall contain reference",
" (base station) receiver observations. At least one RINEX NAV/GNAV/HNAV",
" file shall be included in input files. To use SP3 precise ephemeris, specify",
" the path in the files. The extension of the SP3 file shall be .sp3 or .eph.",
" All of the input file paths can include wild-cards (*). To avoid command",
" line deployment of wild-cards, use \"...\" for paths with wild-cards.",
" Command line options are as follows ([]:default). With -k option, the",
" processing options are input from the configuration file. In this case,",
" command line options precede options in the configuration file.",
"",
" -?        print help",
" -k file   input options from configuration file [off]",
" -o file   set output file [stdout]",
" -ts ds ts start day/time (ds=y/m/d ts=h:m:s) [obs start time]",
" -te de te end day/time   (de=y/m/d te=h:m:s) [obs end time]",
" -ti tint  time interval (sec) [all]",
" -p mode   mode (0:single,1:dgps,2:kinematic,3:static,4:moving-base,",
"                 5:fixed,6:ppp-kinematic,7:ppp-static) [2]",
" -m mask   elevation mask angle (deg) [15]",
" -sys s[,s...] nav system(s) (s=G:GPS,R:GLO,E:GAL,J:QZS,C:BDS,I:IRN) [G|R]",
" -f freq   number of frequencies for relative mode (1:L1,2:L1+L2,3:L1+L2+L5) [2]",
" -v thres  validation threshold for integer ambiguity (0.0:no AR) [3.0]",
" -b        backward solutions [off]",
" -c        forward/backward combined solutions [off]",
" -i        instantaneous integer ambiguity resolution [off]",
" -h        fix and hold for integer ambiguity resolution [off]",
" -e        output x/y/z-ecef position [latitude/longitude/height]",
" -a        output e/n/u-baseline [latitude/longitude/height]",
" -n        output NMEA-0183 GGA sentence [off]",
" -g        output latitude/longitude in the form of ddd mm ss.ss' [ddd.ddd]",
" -t        output time in the form of yyyy/mm/dd hh:mm:ss.ss [sssss.ss]",
" -u        output time in utc [gpst]",
" -d col    number of decimals in time [3]",
" -s sep    field separator [' ']",
" -r x y z  reference (base) receiver ecef pos (m) [average of single pos]",
"           rover receiver ecef pos (m) for fixed or ppp-fixed mode",
" -l lat lon hgt reference (base) receiver latitude/longitude/height (deg/m)",
"           rover latitude/longitude/height for fixed or ppp-fixed mode",
" -y level  output soltion status (0:off,1:states,2:residuals) [0]",
" -x level  debug trace level (0:off) [0]"
};
/* show message --------------------------------------------------------------*/
extern int showmsg(const char *format, ...)
{
    va_list arg;
    va_start(arg,format); vfprintf(stderr,format,arg); va_end(arg);
    fprintf(stderr,"\r");
    return 0;
}
extern void settspan(gtime_t ts, gtime_t te) {}
extern void settime(gtime_t time) {}

/* print help ----------------------------------------------------------------*/
static void printhelp(void)
{
    int i;
    for (i=0;i<(int)(sizeof(help)/sizeof(*help));i++) fprintf(stderr,"%s\n",help[i]);
    exit(0);
}
/* rnx2rtkp main -------------------------------------------------------------*/
int main(int argc, char **argv)
{//����porcopt_t .solopt_t . filopt_t�������ڽ��ܶ�ȡ��������
    prcopt_t prcopt=prcopt_default;//��λ����ģʽ
    solopt_t solopt=solopt_default;// ��������ʽ
    filopt_t filopt={""};// �ļ�·��ѡ��
    gtime_t ts={0},te={0};// ts��ʼʱ�䡢te����ʱ��
    double tint=0.0,es[]={2000,1,1,0,0,0},ee[]={2000,12,31,23,59,59},pos[3];
    int i,// forѭ���ļ���
        j,// Ƕ�׵�forѭ������
        n,// ��¼�����ļ���
        ret;// ����postpos�ķ���ֵ
    char *infile[MAXFILE],// �����ļ���Ĭ�����16�����ɸ�MAXFILE����
        *outfile="",// ����ļ�
        *p;// ָ���ַ�����ָ�룬����ѭ��ָ���main��������
    
    prcopt.mode  =PMODE_KINEMA;// ��λģʽĬ�϶�̬��Զ�λKinematic
    prcopt.navsys=0;// ����ϵͳ����������
    prcopt.refpos=1;// ��׼վ���꣬����Ϊ��SPPƽ����õ�
    prcopt.glomodear=1;// GLONASS AR mode,����on
    solopt.timef=0;// ���ʱ���ʽ������sssss.s
    sprintf(solopt.prog ,"%s ver.%s %s",PROGNAME,VER_RTKLIB,PATCH_LEVEL);
    sprintf(filopt.trace,"%s.trace",PROGNAME);
    
    /* load options from configuration file */
    for (i=1;i<argc;i++) {
        if (!strcmp(argv[i],"-k")&&i+1<argc) {// �����-k�������ļ�����
            resetsysopts();// ��������������
            if (!loadopts(argv[++i],sysopts)) return -1;// �ٶ�ȡ�����ļ����ݣ�����opt_t��sysopt��(��ȡ�����ļ�Ϊ����׼����sysopt�洢�ľ��������ļ���Ϣ)
            getsysopts(&prcopt,&solopt,&filopt);// opt_tת��porcopt_t/solopt_t/filopt_t
        }
    }
    // for ѭ���ж� main ��������
    for (i=1,n=0;i<argc;i++) {
        if      (!strcmp(argv[i],"-o")&&i+1<argc) outfile=argv[++i];//��ȡ����ļ�·������ֵ��outfile
        else if (!strcmp(argv[i],"-ts")&&i+2<argc) {// ��ȡ��ʼ����ʱ��
            sscanf(argv[++i],"%lf/%lf/%lf",es,es+1,es+2);
            sscanf(argv[++i],"%lf:%lf:%lf",es+3,es+4,es+5);
            ts=epoch2time(es); // תΪgtime_t
        }
        else if (!strcmp(argv[i],"-te")&&i+2<argc) { // ��ȡ��������ʱ��
            sscanf(argv[++i],"%lf/%lf/%lf",ee,ee+1,ee+2);
            sscanf(argv[++i],"%lf:%lf:%lf",ee+3,ee+4,ee+5);
            te=epoch2time(ee);// תΪgtime_t
        }
        else if (!strcmp(argv[i],"-ti")&&i+1<argc) tint=atof(argv[++i]);// ��ȡ����ʱ����Ƶ��
        else if (!strcmp(argv[i],"-k")&&i+1<argc) {++i; continue;}// ��-k������
        else if (!strcmp(argv[i],"-p")&&i+1<argc) prcopt.mode=atoi(argv[++i]);// ��ȡ����ģʽ
        else if (!strcmp(argv[i],"-f")&&i+1<argc) prcopt.nf=atoi(argv[++i]);// ��ȡ���ڼ����Ƶ��
        else if (!strcmp(argv[i],"-sys")&&i+1<argc) {// ��ȡ���ڼ���ĵ���ϵͳ
            for (p=argv[++i];*p;p++) {
                switch (*p) {//�ж�Ӧ����ϵͳ���Ͱ������������������
                    case 'G': prcopt.navsys|=SYS_GPS;
                    case 'R': prcopt.navsys|=SYS_GLO;
                    case 'E': prcopt.navsys|=SYS_GAL;
                    case 'J': prcopt.navsys|=SYS_QZS;
                    case 'C': prcopt.navsys|=SYS_CMP;
                    case 'I': prcopt.navsys|=SYS_IRN;
                }
                if (!(p=strchr(p,','))) break;
            }
        }
        else if (!strcmp(argv[i],"-m")&&i+1<argc) prcopt.elmin=atof(argv[++i])*D2R;// ���ý�ֹ�߶Ƚ�
        else if (!strcmp(argv[i],"-v")&&i+1<argc) prcopt.thresar[0]=atof(argv[++i]);// ��������ģ����Ratioֵ
        else if (!strcmp(argv[i],"-s")&&i+1<argc) strcpy(solopt.sep,argv[++i]);// �����ļ�·���ָ���
        else if (!strcmp(argv[i],"-d")&&i+1<argc) solopt.timeu=atoi(argv[++i]);// ����ʱ��С��λ��
        else if (!strcmp(argv[i],"-b")) prcopt.soltype=1;// �����˲�
        else if (!strcmp(argv[i],"-c")) prcopt.soltype=2;// ǰ�����˲����
        else if (!strcmp(argv[i],"-i")) prcopt.modear=2;// ����Ԫģ���ȹ̶�
        else if (!strcmp(argv[i],"-h")) prcopt.modear=3;// fix and hold ģ���ȹ̶�
        else if (!strcmp(argv[i],"-t")) solopt.timef=1;// ���ʱ���ʽΪ yyyy/mm/dd hh:mm:ss.ss
        else if (!strcmp(argv[i],"-u")) solopt.times=TIMES_UTC;// ���Ϊ UTC ʱ��
        else if (!strcmp(argv[i],"-e")) solopt.posf=SOLF_XYZ;// ��� XYZ-ecef ����
        else if (!strcmp(argv[i],"-a")) solopt.posf=SOLF_ENU;// ��� ENU-baseline
        else if (!strcmp(argv[i],"-n")) solopt.posf=SOLF_NMEA;// ��� NMEA-0183 GGA
        else if (!strcmp(argv[i],"-g")) solopt.degf=1;// �����γ�ȸ�ʽΪ ddd mm ss.ss
        else if (!strcmp(argv[i],"-r")&&i+3<argc) {// ��վλ��E CEF-XYZ (m)
            prcopt.refpos=prcopt.rovpos=0;// ��׼վ������վλ�ö�����0
            for (j=0;j<3;j++) prcopt.rb[j]=atof(argv[++i]);// ѭ�������׼վ����
            matcpy(prcopt.ru,prcopt.rb,3,1);
        }
        else if (!strcmp(argv[i],"-l")&&i+3<argc) {   // ѭ�������վλ�û�վλ��LLH (deg/m)
            prcopt.refpos=prcopt.rovpos=0;    // ��׼վ������վλ�ö�����0
            for (j=0;j<3;j++) pos[j]=atof(argv[++i]);
            for (j=0;j<2;j++) pos[j]*=D2R;   // �Ƕ�ת����
            pos2ecef(pos,prcopt.rb);        // LLH ת XYZ
            matcpy(prcopt.ru,prcopt.rb,3,1);
        }
        else if (!strcmp(argv[i],"-y")&&i+1<argc) solopt.sstat=atoi(argv[++i]);     //��������Ϣ
        else if (!strcmp(argv[i],"-x")&&i+1<argc) solopt.trace=atoi(argv[++i]);     //���debug trace�ȼ�
        else if (*argv[i]=='-') printhelp();    //����-����ӡ����
        else if (n<MAXFILE) infile[n++]=argv[i];    //ѭ���ж���һ�����֮����Ϊ�������ļ�·������infile�������
    }
    if (!prcopt.navsys) {       //���û������ϵͳ��Ĭ��ΪGPS��GLONASS
        prcopt.navsys=SYS_GPS|SYS_GLO;
    }
    if (n<=0) {     //��������ļ���Ϊ0,������-2�˳�
        showmsg("error : no input file");
        return -2;
    }

        //   gtime_t ts       I   processing start time (ts.time==0: no limit)
        //   gtime_t te       I   processing end time   (te.time==0: no limit)
        //   double ti        I   processing interval  (s) (0:all)
        //   double tu        I   processing unit time (s) (0:all)
        //   prcopt_t *popt   I   processing options
        //   solopt_t *sopt   I   solution options
        //   filopt_t *fopt   I   file options
        //   char   **infile  I   input files (see below)
        //   int    n         I   number of input files
        //   char   *outfile  I   output file ("":stdout, see below)
        //   char   *rov      I   rover id list        (separated by " ")
        //   char   *base     I   base station id list (separated by " ")
        //������λ����


    ret=postpos(ts,te,tint,0.0,&prcopt,&solopt,&filopt,infile,n,outfile,"","");
    
    if (!ret) fprintf(stderr,"%40s\r","");
    return ret;
}