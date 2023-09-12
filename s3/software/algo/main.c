int main() {
	double array[] = {1.2, -2.5, 6.0, 88, -12.8};
	double i = 0;
	double j = 0;
	double* p = array;
	double* q = p + 3;
	
	p[q - 1] = q[j - 3];

	return 0;
}
